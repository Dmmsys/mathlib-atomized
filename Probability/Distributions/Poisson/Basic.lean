/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion, Hanzhang Cheng
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers. For `r : ℝ≥0`, `poissonMeasure r` is the
measure which to `{n}` associates `exp (-r) * r ^ n / (n)!`.

## Main definition

* `poissonMeasure r`: a Poisson measure on `ℕ`, parametrized by its rate `r : ℝ≥0`.

## Main results

* `poissonMeasure_conv_poissonMeasure`: `Poisson(r₁) ∗ Poisson(r₂) = Poisson(r₁ + r₂)`.
* `IndepFun.hasLaw_add_poissonMeasure`: the sum of two independent Poisson random variables
  is again Poisson.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The poisson measure with rate `r : ℝ≥0` as a measure over `ℕ`. -/
@[wikidata Q205692]
noncomputable
/-
**ProbabilityTheory.poissonMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`
。
形式化陈述：poissonMeasure (r : Real>=0) : Measure Nat
参数：r : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def poissonMeasure (r : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

/-- The Poisson probability distribution with rate `r`. -/
scoped notation3 "Po(" r ")" => poissonMeasure r

/-- The Poisson probability distribution with rate `r` valued in the `AddMonoidWithOne` `R`. -/
scoped notation3 "Po(" R ", " r ")" => (poissonMeasure r).map (Nat.cast : ℕ → R)

/-
**ProbabilityTheory.poissonMeasure_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：poissonMeasure_singleton (r : Real>=0) (n : Nat) : Po(r) {n} = ENNReal.ofR
eal (exp (-r) * r ^ n / (n)!)
参数：r : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.poissonMeasure.eq_1`：∀ (r : NNReal),   ProbabilityTheo
ry.poissonMeasure r =     MeasureTheory.Measure.sum fun n =>       ENNReal.ofRea
l (Real.exp (-↑r) * ↑r ^ n …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.sum_smul_dirac_singleton`：sum_smul_dirac_singleton
 [MeasurableSingletonClass α] {f : α -> Real>=0∞} {a : α} : sum (fun b : α => f 
b • dirac b) {a} = f a
-/
lemma poissonMeasure_singleton (r : ℝ≥0) (n : ℕ) :
    Po(r) {n} = ENNReal.ofReal (exp (-r) * r ^ n / (n)!) := by
  rw [poissonMeasure, Measure.sum_smul_dirac_singleton]
/-
**ProbabilityTheory.poissonMeasure_real_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：poissonMeasure_real_singleton (r : Real>=0) (n : Nat) : Po(r).real {n} = e
xp (-r) * r ^ n / (n)!
参数：r : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用引理 `ProbabilityTheory.poissonMeasure_singleton`：poissonMeasure_singleton (r 
: Real>=0) (n : Nat) : Po(r) {n} = ENNReal.ofReal (exp (-r) * r ^ n / (n)!)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
lemma poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    Po(r).real {n} = exp (-r) * r ^ n / (n)! := by
  rw [measureReal_def, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]
/-
**ProbabilityTheory.poissonMeasure_real_singleton_pos** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：poissonMeasure_real_singleton_pos {r : Real>=0} (n : Nat) (hr : 0 < r) : 0
 < Po(r).real {n}
参数：n : Nat；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.poissonMeasure_real_singleton`：poissonMeasure_real_sin
gleton (r : Real>=0) (n : Nat) : Po(r).real {n} = exp (-r) * r ^ n / (n)!
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
lemma poissonMeasure_real_singleton_pos {r : ℝ≥0} (n : ℕ) (hr : 0 < r) :
    0 < Po(r).real {n} := by
  rw [poissonMeasure_real_singleton]
  positivity
/-
**ProbabilityTheory.hasSum_one_poissonMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：hasSum_one_poissonMeasure (r : Real>=0) : HasSum (fun n => exp (-r) * r ^ 
n / (n)!) 1
参数：r : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedSpace.expSeries_div_hasSum_exp`：expSeries_div_hasSum_exp (x : 𝔸) :
 HasSum (fun n => x ^ n / n !) (exp x)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma hasSum_one_poissonMeasure (r : ℝ≥0) : HasSum (fun n ↦ exp (-r) * r ^ n / (n)!) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_ℝ, ← exp_add]
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : ℝ≥0) : IsProbabilityMeasure Po(r) :=
  (hasSum_one_poissonMeasure r).isProbabilityMeasure_sum_dirac (fun _ ↦ by positivity)
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : ℝ≥0) {R : Type*} [NatCast R] [MeasurableSpace R] :
    IsProbabilityMeasure Po(R, r) :=
  Measure.isProbabilityMeasure_map .of_discrete

section Integral

variable {E : Type*} [NormedAddCommGroup E]
variable {R : Type*} [NatCast R] [MeasurableSpace R]

/-
**ProbabilityTheory.integrable_poissonMeasure_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：integrable_poissonMeasure_iff {r : Real>=0} {f : Nat -> E} : Integrable f 
Po(r) ↔ Summable (fun n => exp (-r) * r ^ n / (n)! * ‖f n‖)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.poissonMeasure.eq_1`：∀ (r : NNReal),   ProbabilityTheo
ry.poissonMeasure r =     MeasureTheory.Measure.sum fun n =>       ENNReal.ofRea
l (Real.exp (-↑r) * ↑r ^ n …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
lemma integrable_poissonMeasure_iff {r : ℝ≥0} {f : ℕ → E} :
    Integrable f Po(r) ↔ Summable (fun n ↦ exp (-r) * r ^ n / (n)! * ‖f n‖) := by
  rw [poissonMeasure, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]
/-
**ProbabilityTheory.integrable_map_cast_poissonMeasure_iff** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：integrable_map_cast_poissonMeasure_iff {r : Real>=0} [Countable R] [Measur
ableSingletonClass R] {f : R -> E} : Integrable f Po(R, r) ↔ Integrable (f ∘ Nat
.cast) Po(r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_discrete`：of_discrete [Countable α
] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ
· 使用引理 `AEMeasurable.of_discrete`：of_discrete [DiscreteMeasurableSpace α] : AEMe
asurable f μ
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
-/
lemma integrable_map_cast_poissonMeasure_iff {r : ℝ≥0} [Countable R] [MeasurableSingletonClass R]
  {f : R → E} : Integrable f Po(R, r) ↔ Integrable (f ∘ Nat.cast) Po(r) :=
  integrable_map_measure .of_discrete .of_discrete

variable [NormedSpace ℝ E]
/-
**ProbabilityTheory.hasSum_integral_poissonMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：hasSum_integral_poissonMeasure [CompleteSpace E] {r : Real>=0} {f : Nat ->
 E} (hf : Integrable f Po(r)) : HasSum (fun n => (exp (-r) * r ^ n / (n)!) • f n
) (∫ n, f n ∂Po(r))
参数：hf : Integrable f Po(r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
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
· 使用引理 `ProbabilityTheory.integrable_poissonMeasure_iff`：integrable_poissonMeasu
re_iff {r : Real>=0} {f : Nat -> E} : Integrable f Po(r) ↔ Summable (fun n => ex
p (-r) * r ^ n / (n)! * ‖f n‖)
-/
lemma hasSum_integral_poissonMeasure [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f Po(r)) :
    HasSum (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) (∫ n, f n ∂Po(r)) := by
  have : (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) =
      fun n ↦ (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert! integrable_poissonMeasure_iff.1 hf
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- If a function is integrable with respect to `poissonMeasure r`, then its integral
against this measure is given by its sum weighted by `exp (-r) * r ^ n / n!`.

See `integral_poissonMeasure` for a version where the codomain is finite-dimensional
and does not require the integrability hypothesis. -/
/-
**ProbabilityTheory.integral_poissonMeasure'** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：integral_poissonMeasure' [CompleteSpace E] {r : Real>=0} {f : Nat -> E} (h
f : Integrable f Po(r)) : ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f 
n
参数：hf : Integrable f Po(r)。
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
· 使用引理 `ProbabilityTheory.hasSum_integral_poissonMeasure`：hasSum_integral_poisso
nMeasure [CompleteSpace E] {r : Real>=0} {f : Nat -> E} (hf : Integrable f Po(r)
) : HasSum (fun n => (exp (-r) * r ^ n…

--- 原说明 ---
If a function is integrable with respect to `poissonMeasure r`, then its integra
l
against this measure is given by its sum weighted by `exp (-r) * r ^ n / n!`.

See `integral_poissonMeasure` for a version where the codomain is finite-dimensi
onal
and does not require the integrability hypothesis.
-/
lemma integral_poissonMeasure' [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f Po(r)) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n :=
  (hasSum_integral_poissonMeasure hf).tsum_eq.symm
/-
**ProbabilityTheory.integral_map_cast_poissonMeasure'** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：integral_map_cast_poissonMeasure' [CompleteSpace E] [Countable R] [Measura
bleSingletonClass R] {r : Real>=0} {f : R -> E} (hf : Integrable f Po(R, r)) : ∫
 x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n
参数：hf : Integrable f Po(R, r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用引理 `AEMeasurable.of_discrete`：of_discrete [DiscreteMeasurableSpace α] : AEMe
asurable f μ
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_discrete`：of_discrete [Countable α
] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ
· 使用引理 `ProbabilityTheory.integral_poissonMeasure'`：integral_poissonMeasure' [Co
mpleteSpace E] {r : Real>=0} {f : Nat -> E} (hf : Integrable f Po(r)) : ∫ n, f n
 ∂Po(r) = ∑' n, (exp (-r) * r ^ …
· 使用引理 `ProbabilityTheory.integrable_map_cast_poissonMeasure_iff`：integrable_map
_cast_poissonMeasure_iff {r : Real>=0} [Countable R] [MeasurableSingletonClass R
] {f : R -> E} : Integrable f Po(R, r) ↔ Integ…
-/
lemma integral_map_cast_poissonMeasure' [CompleteSpace E] [Countable R] [MeasurableSingletonClass R]
    {r : ℝ≥0} {f : R → E} (hf : Integrable f Po(R, r)) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [integral_map .of_discrete .of_discrete]
  rw [integrable_map_cast_poissonMeasure_iff] at hf
  exact integral_poissonMeasure' hf

/-- The integral of a function taking values in a finite-dimensional space
against `poissonMeasure r` is given by its sum weighted by `exp (-r) * r ^ n / n!`. This version
does not require integrability, as the integral exists if and only if the sum exists, and otherwise
they are both defined to be zero.

See `integral_poissonMeasure'` with a general codomain which assumes integrability. -/
/-
**ProbabilityTheory.integral_poissonMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：integral_poissonMeasure [FiniteDimensional Real E] (r : Real>=0) (f : Nat 
-> E) : ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n
参数：r : Real>=0；f : Nat -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.poissonMeasure.eq_1`：∀ (r : NNReal),   ProbabilityTheo
ry.poissonMeasure r =     MeasureTheory.Measure.sum fun n =>       ENNReal.ofRea
l (Real.exp (-↑r) * ↑r ^ n …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial

--- 原说明 ---
The integral of a function taking values in a finite-dimensional space
against `poissonMeasure r` is given by its sum weighted by `exp (-r) * r ^ n / n
!`. This version
does not require integrability, as the integral exists if and only if the sum ex
ists, and otherwise
they are both defined to be zero.

See `integral_poissonMeasure'` with a general codomain which assumes integrabili
ty.
-/
lemma integral_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) (f : ℕ → E) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [poissonMeasure, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]
/-
**ProbabilityTheory.integral_map_cast_poissonMeasure** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：integral_map_cast_poissonMeasure [FiniteDimensional Real E] (r : Real>=0) 
[Countable R] [MeasurableSingletonClass R] (f : R -> E) : ∫ x, f x ∂Po(R, r) = ∑
' n, (exp (-r) * r ^ n / (n)!) • f n
参数：r : Real>=0；f : R -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用引理 `AEMeasurable.of_discrete`：of_discrete [DiscreteMeasurableSpace α] : AEMe
asurable f μ
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_discrete`：of_discrete [Countable α
] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ
· 使用引理 `ProbabilityTheory.integral_poissonMeasure`：integral_poissonMeasure [Fini
teDimensional Real E] (r : Real>=0) (f : Nat -> E) : ∫ n, f n ∂Po(r) = ∑' n, (ex
p (-r) * r ^ n / (n)!) • f n
-/
lemma integral_map_cast_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) [Countable R]
  [MeasurableSingletonClass R] (f : R → E) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [integral_map .of_discrete .of_discrete, integral_poissonMeasure]

end Integral

section CharFun

open Complex

/-- The characteristic function of the Poisson distribution with rate `r` is
`t ↦ exp(r(exp(it) - 1))`. -/
/-
**ProbabilityTheory.charFun_map_cast_poissonMeasure** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：charFun_map_cast_poissonMeasure (r : Real>=0) (t : Real) : charFun Po(Real
, r) t = cexp (r * (cexp (t * I) - 1))
参数：r : Real>=0；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_apply`：charFun_apply [Inner Real E] (t : E) : char
Fun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用引理 `AEMeasurable.of_discrete`：of_discrete [DiscreteMeasurableSpace α] : AEMe
asurable f μ
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用引理 `MeasureTheory.AEStronglyMeasurable.inner_const`：inner_const (hf : AEStro
nglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (⟪f ·, c⟫) μ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.integral_poissonMeasure`：integral_poissonMeasure [Fini
teDimensional Real E] (r : Real>=0) (f : Nat -> E) : ∫ n, f n ∂Po(r) = ∑' n, (ex
p (-r) * r ^ n / (n)!) • f n
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.inner_apply`：Real.inner_apply (x y : Real) : inner Real x y = x * y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic function of the Poisson distribution with rate `r` is
`t ↦ exp(r(exp(it) - 1))`.
-/
lemma charFun_map_cast_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    charFun Po(ℝ, r) t = cexp (r * (cexp (t * I) - 1)) := by
  rw [charFun_apply, integral_map .of_discrete (by fun_prop), integral_poissonMeasure r]
  simp_rw [Real.inner_apply]
  calc ∑' a, (rexp (-r) * r ^ a / a ! : ℝ) * cexp ((a * t : ℝ) * I)
  _ = ∑' a, (rexp (-r)) * ((r * cexp (t * I)) ^ a / a !) := by
      congr with a
      push_cast
      rw [mul_pow, ← Complex.exp_nat_mul]
      ring_nf
  _ = (rexp (-r)) * ∑' a, ((r * cexp (t * I)) ^ a / a !) := tsum_mul_left
  _ = (rexp (-r)) * cexp (r * cexp (t * I)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (r * cexp (t * I))).tsum_eq, exp_eq_exp_ℂ]
  _ = cexp (r * (cexp (t * I) - 1)) := by
      rw [ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf

end CharFun

/-! ### Convolution of Poisson measures -/

section Convolution

variable {R : Type*} [AddMonoidWithOne R] {mR : MeasurableSpace R}

/-
**ProbabilityTheory.map_cast_poissonMeasure_conv_real** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem map_cast_poissonMeasure_conv_real (r₁ r₂ : ℝ≥0) :
    Po(ℝ, r₁) ∗ Po(ℝ, r₂) = Po(ℝ, r₁ + r₂) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr; push_cast; ring
/-
**ProbabilityTheory.poissonMeasure_conv_poissonMeasure** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：poissonMeasure_conv_poissonMeasure (r₁ r₂ : Real>=0) : Po(r₁) ∗ Po(r₂) = P
o(r₁ + r₂)
参数：r₁ r₂ : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.map_injective`：map_injective (hf : MeasurableEmbeddi
ng f) : Function.Injective (Measure.map f)
· 使用引理 `MeasurableEmbedding.natCast`：natCast {α : Type*} [MeasurableSpace α] [Me
asurableSingletonClass α] [AddMonoidWithOne α] [CharZero α] : MeasurableEmbeddin
g (Nat.cast : Nat…
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
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.coe_castAddMonoidHom`：coe_castAddMonoidHom [AddMonoidWithOne α] : (c
astAddMonoidHom α : Nat -> α) = Nat.cast
· 使用定理 `MeasureTheory.Measure.map_conv_addMonoidHom`：∀ {M : Type u_2} {M' : Type
 u_3} {mM : MeasurableSpace M} [inst : AddMonoid M] [MeasurableAdd₂ M]   {mM' : 
MeasurableSpace M'} [inst_2 : Add…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `TopologicalSpace.Countable.to_separableSpace`：∀ {α : Type u} [t : Topolo
gicalSpace α] [Countable α], TopologicalSpace.SeparableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalSemiring`：∀ {R : Type u_1} [inst : Topologic
alSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [DiscreteTopology R],   IsTopo
logicalSemiring R
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 35 条，此处仅展示前 30 条）
-/
theorem poissonMeasure_conv_poissonMeasure (r₁ r₂ : ℝ≥0) :
    Po(r₁) ∗ Po(r₂) = Po(r₁ + r₂) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [← Nat.coe_castAddMonoidHom, Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_poissonMeasure_conv_real _ _
/-
**ProbabilityTheory.map_cast_poissonMeasure_conv** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：map_cast_poissonMeasure_conv [MeasurableAdd₂ R] (r₁ r₂ : Real>=0) : Po(R, 
r₁) ∗ Po(R, r₂) = Po(R, r₁ + r₂)
参数：r₁ r₂ : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.coe_castAddMonoidHom`：coe_castAddMonoidHom [AddMonoidWithOne α] : (c
astAddMonoidHom α : Nat -> α) = Nat.cast
· 使用定理 `MeasureTheory.Measure.map_conv_addMonoidHom`：∀ {M : Type u_2} {M' : Type
 u_3} {mM : MeasurableSpace M} [inst : AddMonoid M] [MeasurableAdd₂ M]   {mM' : 
MeasurableSpace M'} [inst_2 : Add…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.Countable.to_separableSpace`：∀ {α : Type u} [t : Topolo
gicalSpace α] [Countable α], TopologicalSpace.SeparableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalSemiring`：∀ {R : Type u_1} [inst : Topologic
alSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [DiscreteTopology R],   IsTopo
logicalSemiring R
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `MeasureTheory.instSFiniteOfCountable`：∀ {α : Type u_1} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [Countable α], MeasureTheory.SFinite μ
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`：poissonMeasure_con
v_poissonMeasure (r₁ r₂ : Real>=0) : Po(r₁) ∗ Po(r₂) = Po(r₁ + r₂)
-/
theorem map_cast_poissonMeasure_conv [MeasurableAdd₂ R] (r₁ r₂ : ℝ≥0) :
    Po(R, r₁) ∗ Po(R, r₂) = Po(R, r₁ + r₂) := by
  rw [← Nat.coe_castAddMonoidHom, ← Measure.map_conv_addMonoidHom _ (by fun_prop),
    poissonMeasure_conv_poissonMeasure]

/-- The sum of two independent Poisson random variables with rates `r₁, r₂` is a Poisson
random variable with rate `r₁ + r₂`. -/
/-
**ProbabilityTheory.IndepFun.hasLaw_add_poissonMeasure** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {r
₁ r₂ : NNReal} {X Y : Ω → ℕ},   ProbabilityTheory.IndepFun X Y P →     Probabili
tyTheory.HasLaw X (ProbabilityTheory.poissonMeasure r₁) P →       ProbabilityThe
ory.HasLaw Y (ProbabilityTheory.poissonMeasure r₂) P →         ProbabilityTheory
.HasLaw (X + Y) (ProbabilityTheory.poissonMeasure (r₁ + r₂)) P
参数：ProbabilityTheory.poissonMeasure r₁；ProbabilityTheory.poissonMeasure r₂；X + Y
；ProbabilityTheory.poissonMeasure (r₁ + r₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`：poissonMeasure_con
v_poissonMeasure (r₁ r₂ : Real>=0) : Po(r₁) ∗ Po(r₂) = Po(r₁ + r₂)
· 使用定理 `ProbabilityTheory.IndepFun.hasLaw_add`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {P : MeasureTheory.Measure Ω} {M : Type u_3} [inst : AddMonoid M]   {mM
 : MeasurableSpace M} [Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.Countable.to_separableSpace`：∀ {α : Type u} [t : Topolo
gicalSpace α] [Countable α], TopologicalSpace.SeparableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalSemiring`：∀ {R : Type u_1} [inst : Topologic
alSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [DiscreteTopology R],   IsTopo
logicalSemiring R
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.instRegularOfBorelSpaceOf
R1SpaceOfIsFiniteMeasure`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : Measu
reTheory.Measure α} [inst_1 : TopologicalSpace α] [BorelSpace α]   [R1Space α] [
h : μ.…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of two independent Poisson random variables with rates `r₁, r₂` is a Poi
sson
random variable with rate `r₁ + r₂`.
-/
theorem IndepFun.hasLaw_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {r₁ r₂ : ℝ≥0} {X Y : Ω → ℕ}
    (hXY : IndepFun X Y P) (hX : HasLaw X Po(r₁) P) (hY : HasLaw Y Po(r₂) P) :
    HasLaw (X + Y) Po(r₁ + r₂) P := by
  rw [← poissonMeasure_conv_poissonMeasure]
  exact hXY.hasLaw_add hX hY

/-- The sum of two independent Poisson random variables with rates `r₁, r₂` taking values in `R`
is a Poisson random variable with rate `r₁ + r₂`. -/
/-
**ProbabilityTheory.IndepFun.hasLaw_add_map_cast_poissonMeasure** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] {mR : MeasurableSpace R} {Ω :
 Type u_2} {mΩ : MeasurableSpace Ω}   {P : MeasureTheory.Measure Ω} [MeasurableA
dd₂ R] {r₁ r₂ : NNReal} {X Y : Ω → R},   ProbabilityTheory.IndepFun X Y P →     
ProbabilityTheory.HasLaw X (MeasureTheory.Measure.map Nat.cast (ProbabilityTheor
y.poissonMeasure r₁)) P →       ProbabilityTheory.HasLaw Y (MeasureTheory.Measur
e.map Nat.cast (ProbabilityTheory.poissonMeasure r₂)) P →         ProbabilityThe
ory.HasLaw (X + Y)           (MeasureTheory.Measure.map Nat.cast (ProbabilityThe
ory.poissonMeasure (r₁ + r₂))) P
参数：MeasureTheory.Measure.map Nat.cast (ProbabilityTheory.poissonMeasure r₁)；Meas
ureTheory.Measure.map Nat.cast (ProbabilityTheory.poissonMeasure r₂)；X + Y；Measu
reTheory.Measure.map Nat.cast (ProbabilityTheory.poissonMeasure (r₁ + r₂))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.map_cast_poissonMeasure_conv`：map_cast_poissonMeasure_
conv [MeasurableAdd₂ R] (r₁ r₂ : Real>=0) : Po(R, r₁) ∗ Po(R, r₂) = Po(R, r₁ + r
₂)
· 使用定理 `ProbabilityTheory.IndepFun.hasLaw_add`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {P : MeasureTheory.Measure Ω} {M : Type u_3} [inst : AddMonoid M]   {mM
 : MeasurableSpace M} [Meas…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure`：∀ (r : NNRe
al), MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.poissonMeasure r)

--- 原说明 ---
The sum of two independent Poisson random variables with rates `r₁, r₂` taking v
alues in `R`
is a Poisson random variable with rate `r₁ + r₂`.
-/
theorem IndepFun.hasLaw_add_map_cast_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [MeasurableAdd₂ R] {r₁ r₂ : ℝ≥0} {X Y : Ω → R}
    (hXY : IndepFun X Y P) (hX : HasLaw X Po(R, r₁) P) (hY : HasLaw Y Po(R, r₂) P) :
    HasLaw (X + Y) Po(R, r₁ + r₂) P := by
  rw [← map_cast_poissonMeasure_conv]
  exact hXY.hasLaw_add hX hY

end Convolution

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
/-
**ProbabilityTheory.poissonPMFReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`
。
形式化陈述：poissonPMFReal (r : Real>=0) (n : Nat) : Real
参数：r : Real>=0；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / (n)!

@[deprecated (since := "2026-03-08")]
alias poissonPMFRealSum := hasSum_one_poissonMeasure

@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]
/-
**ProbabilityTheory.poissonPMFReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：poissonPMFReal_pos {r : Real>=0} {n : Nat} (hr : 0 < r) : 0 < poissonPMFRe
al r n
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.poissonPMFReal.eq_1`：∀ (r : NNReal) (n : ℕ), Probabili
tyTheory.poissonPMFReal r n = Real.exp (-↑r) * ↑r ^ n / ↑n.factorial
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
lemma poissonPMFReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

@[deprecated measureReal_nonneg (since := "2026-03-08")]
/-
**ProbabilityTheory.poissonPMFReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：poissonPMFReal_nonneg {r : Real>=0} {n : Nat} : 0 <= poissonPMFReal r n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
/-
**ProbabilityTheory.poissonPMF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：poissonPMF (r : Real>=0) : PMF Nat
参数：r : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def poissonPMF (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n ↦ poissonPMFReal_nonneg)

@[deprecated poissonMeasure (since := "2026-03-08")]
/-
**ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：poissonPMFReal_ofReal_eq_poissonPMF (r : Real>=0) (n : Nat) : ENNReal.ofRe
al (poissonPMFReal r n) = poissonPMF r n
参数：r : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma poissonPMFReal_ofReal_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal (poissonPMFReal r n) = poissonPMF r n := by
  simpa only [poissonPMF] using by rfl

@[deprecated Measurable.of_discrete (since := "2026-03-08")]
/-
**ProbabilityTheory.measurable_poissonPMFReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：measurable_poissonPMFReal (r : Real>=0) : Measurable (poissonPMFReal r)
参数：r : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
-/
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
/-
**ProbabilityTheory.stronglyMeasurable_poissonPMFReal** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：stronglyMeasurable_poissonPMFReal (r : Real>=0) : StronglyMeasurable (pois
sonPMFReal r)
参数：r : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : Topologic
alSpace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.measurable_poissonPMFReal`：measurable_poissonPMFReal (
r : Real>=0) : Measurable (poissonPMFReal r)
-/
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

end ProbabilityTheory

