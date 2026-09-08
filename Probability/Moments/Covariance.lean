/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Notation

/-!
# Covariance

We define the covariance of two real-valued random variables.

## Main definitions

* `covariance`: covariance of two real-valued random variables, with notation `cov[X, Y; μ]`.
  `cov[X, Y; μ] = ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`.

## Main statements

* `covariance_self`: `cov[X, X; μ] = Var[X; μ]`

## Notation

* `cov[X, Y; μ] = covariance X Y μ`
* `cov[X, Y] = covariance X Y volume`

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y Z T : Ω → ℝ} {μ : Measure Ω}

/-- The covariance of two real-valued random variables defined as
the integral of `(X - 𝔼[X])(Y - 𝔼[Y])`. -/
/-
**ProbabilityTheory.covariance** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：covariance (X Y : Ω -> Real) (μ : Measure Ω) : Real
参数：X Y : Ω -> Real；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covariance of two real-valued random variables defined as
the integral of `(X - 𝔼[X])(Y - 𝔼[Y])`.
-/
noncomputable def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ

/-- The covariance of the real-valued random variables `X` and `Y`
according to the volume measure. -/
scoped notation "cov[" X ", " Y "]" => cov[X, Y; MeasureTheory.MeasureSpace.volume]

/-
**ProbabilityTheory.covariance_eq_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp 
Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
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
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.MemLp.mul_const`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_3}   [inst : NormedRing 
𝕜] {f : α → 𝕜}, Mea…
· 使用定理 `MeasureTheory.MemLp.const_mul`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_3}   [inst : NormedRing 
𝕜] {f : α → 𝕜}, Mea…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 32 条，此处仅展示前 30 条）
-/
lemma covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
   · exact hY.const_mul _ |>.integrable (by simp)
   · exact integrable_const _
   · exact hX.integrable_mul hY
   · exact hX.mul_const _ |>.integrable (by simp)
   · exact (hX.integrable_mul hY).sub (hX.mul_const _ |>.integrable (by simp))
   · exact (hY.const_mul _ |>.integrable (by simp)).sub (integrable_const _)
/-
**ProbabilityTheory.covariance_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {Y : Ω → ℝ} {μ : MeasureTheory.M
easure Ω},   ProbabilityTheory.covariance 0 Y μ = 0
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma covariance_zero_left : cov[0, Y; μ] = 0 := by simp [covariance]
/-
**ProbabilityTheory.covariance_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {μ : MeasureTheory.M
easure Ω},   ProbabilityTheory.covariance X 0 μ = 0
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma covariance_zero_right : cov[X, 0; μ] = 0 := by simp [covariance]
/-
**ProbabilityTheory.covariance_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ}, ProbabilityTheory
.covariance X Y 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma covariance_zero_measure : cov[X, Y; (0 : Measure Ω)] = 0 := by simp [covariance]

variable (X Y) in
/-
**ProbabilityTheory.covariance_comm** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：covariance_comm : cov[X, Y; μ] = cov[Y, X; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
lemma covariance_comm : cov[X, Y; μ] = cov[Y, X; μ] := by
  simp_rw [covariance]
  congr with x
  ring

@[simp]
/-
**ProbabilityTheory.covariance_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：covariance_const_left [IsProbabilityMeasure μ] (c : Real) : cov[fun _ => c
, Y; μ] = 0
参数：c : Real。
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
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_const_left [IsProbabilityMeasure μ] (c : ℝ) : cov[fun _ ↦ c, Y; μ] = 0 := by
  simp [covariance]

@[simp]
/-
**ProbabilityTheory.covariance_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：covariance_const_right [IsProbabilityMeasure μ] (c : Real) : cov[X, fun _ 
=> c; μ] = 0
参数：c : Real。
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
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_const_right [IsProbabilityMeasure μ] (c : ℝ) : cov[X, fun _ ↦ c; μ] = 0 := by
  simp [covariance]

@[simp]
/-
**ProbabilityTheory.covariance_add_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_add_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (
c : Real) : cov[fun ω => X ω + c, Y; μ] = cov[X, Y; μ]
参数：hX : Integrable X μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_add_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ X ω + c, Y; μ] = cov[X, Y; μ] := by
  simp_rw [covariance]
  congr with ω
  rw [integral_add hX (by fun_prop)]
  simp

@[simp]
/-
**ProbabilityTheory.covariance_const_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_const_add_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (
c : Real) : cov[fun ω => c + X ω, Y; μ] = cov[X, Y; μ]
参数：hX : Integrable X μ；c : Real。
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
· 使用引理 `ProbabilityTheory.covariance_add_const_left`：covariance_add_const_left [
IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) : cov[fun ω => X ω + c,
 Y; μ] = cov[X, Y; μ]
-/
lemma covariance_const_add_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ c + X ω, Y; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_left hX c

@[simp]
/-
**ProbabilityTheory.covariance_add_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_add_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) 
(c : Real) : cov[X, fun ω => Y ω + c; μ] = cov[X, Y; μ]
参数：hY : Integrable Y μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_comm`：covariance_comm : cov[X, Y; μ] = cov[
Y, X; μ]
· 使用引理 `ProbabilityTheory.covariance_add_const_left`：covariance_add_const_left [
IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) : cov[fun ω => X ω + c,
 Y; μ] = cov[X, Y; μ]
-/
lemma covariance_add_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ Y ω + c; μ] = cov[X, Y; μ] := by
  rw [covariance_comm, covariance_add_const_left hY c, covariance_comm]

@[simp]
/-
**ProbabilityTheory.covariance_const_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_const_add_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) 
(c : Real) : cov[X, fun ω => c + Y ω; μ] = cov[X, Y; μ]
参数：hY : Integrable Y μ；c : Real。
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
· 使用引理 `ProbabilityTheory.covariance_add_const_right`：covariance_add_const_right
 [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) : cov[X, fun ω => Y ω
 + c; μ] = cov[X, Y; μ]
-/
lemma covariance_const_add_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ c + Y ω; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_right hY c
/-
**ProbabilityTheory.covariance_add_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covariance_add_left [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2
 μ) (hZ : MemLp Z 2 μ) : cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
（共 44 条，此处仅展示前 30 条）
-/
lemma covariance_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ] := by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
/-
**ProbabilityTheory.covariance_add_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_add_right [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 
2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y + Z; μ] = cov[X, Y; μ] + cov[X, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_comm`：covariance_comm : cov[X, Y; μ] = cov[
Y, X; μ]
· 使用引理 `ProbabilityTheory.covariance_add_left`：covariance_add_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X + Y, Z; 
μ] = cov[X, Z; μ] + cov[Y, …
-/
lemma covariance_add_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y + Z; μ] = cov[X, Y; μ] + cov[X, Z; μ] := by
  rw [covariance_comm, covariance_add_left hY hZ hX, covariance_comm X, covariance_comm Z]
/-
**ProbabilityTheory.covariance_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_smul_left (c : Real) : cov[c • X, Y; μ] = c * cov[X, Y; μ]
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_smul_left (c : ℝ) : cov[c • X, Y; μ] = c * cov[X, Y; μ] := by
  simp_rw [covariance, Pi.smul_apply, smul_eq_mul, ← integral_const_mul, ← mul_assoc, mul_sub,
    integral_const_mul]
/-
**ProbabilityTheory.covariance_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：covariance_smul_right (c : Real) : cov[X, c • Y; μ] = c * cov[X, Y; μ]
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_comm`：covariance_comm : cov[X, Y; μ] = cov[
Y, X; μ]
· 使用引理 `ProbabilityTheory.covariance_smul_left`：covariance_smul_left (c : Real) 
: cov[c • X, Y; μ] = c * cov[X, Y; μ]
-/
lemma covariance_smul_right (c : ℝ) : cov[X, c • Y; μ] = c * cov[X, Y; μ] := by
  rw [covariance_comm, covariance_smul_left, covariance_comm]
/-
**ProbabilityTheory.covariance_const_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_const_mul_left (c : Real) : cov[fun ω => c * X ω, Y; μ] = c * c
ov[X, Y; μ]
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covariance_smul_left`：covariance_smul_left (c : Real) 
: cov[c • X, Y; μ] = c * cov[X, Y; μ]
-/
lemma covariance_const_mul_left (c : ℝ) : cov[fun ω ↦ c * X ω, Y; μ] = c * cov[X, Y; μ] :=
  covariance_smul_left c
/-
**ProbabilityTheory.covariance_const_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_const_mul_right (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * 
cov[X, Y; μ]
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covariance_smul_right`：covariance_smul_right (c : Real
) : cov[X, c • Y; μ] = c * cov[X, Y; μ]
-/
lemma covariance_const_mul_right (c : ℝ) : cov[X, fun ω ↦ c * Y ω; μ] = c * cov[X, Y; μ] :=
  covariance_smul_right c
/-
**ProbabilityTheory.covariance_mul_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_mul_const_left (c : Real) : cov[fun ω => X ω * c, Y; μ] = cov[X
, Y; μ] * c
参数：c : Real。
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
· 使用引理 `ProbabilityTheory.covariance_const_mul_left`：covariance_const_mul_left (
c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_mul_const_left (c : ℝ) : cov[fun ω ↦ X ω * c, Y; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_left]
/-
**ProbabilityTheory.covariance_mul_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_mul_const_right (c : Real) : cov[X, fun ω => Y ω * c; μ] = cov[
X, Y; μ] * c
参数：c : Real。
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
· 使用引理 `ProbabilityTheory.covariance_const_mul_right`：covariance_const_mul_right
 (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_mul_const_right (c : ℝ) : cov[X, fun ω ↦ Y ω * c; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_right]
/-
**ProbabilityTheory.covariance_fun_div_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covariance_fun_div_left (c : Real) : cov[fun ω => X ω / c, Y; μ] = cov[X, 
Y; μ] / c
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.covariance_const_mul_left`：covariance_const_mul_left (
c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_fun_div_left (c : ℝ) :
    cov[fun ω ↦ X ω / c, Y; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_left]
/-
**ProbabilityTheory.covariance_fun_div_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covariance_fun_div_right (c : Real) : cov[X, fun ω => Y ω / c; μ] = cov[X,
 Y; μ] / c
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.covariance_const_mul_right`：covariance_const_mul_right
 (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_fun_div_right (c : ℝ) :
    cov[X, fun ω ↦ Y ω / c; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_right]

@[simp]
/-
**ProbabilityTheory.covariance_neg_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covariance_neg_left : cov[-X, Y; μ] = -cov[X, Y; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.covariance_smul_left`：covariance_smul_left (c : Real) 
: cov[c • X, Y; μ] = c * cov[X, Y; μ]
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma covariance_neg_left : cov[-X, Y; μ] = -cov[X, Y; μ] := by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : ℝ) • X, Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]
/-
**ProbabilityTheory.covariance_fun_neg_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covariance_fun_neg_left : cov[fun ω => -X ω, Y; μ] = -cov[X, Y; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covariance_neg_left`：covariance_neg_left : cov[-X, Y; 
μ] = -cov[X, Y; μ]
-/
lemma covariance_fun_neg_left : cov[fun ω ↦ -X ω, Y; μ] = -cov[X, Y; μ] :=
  covariance_neg_left

@[simp]
/-
**ProbabilityTheory.covariance_neg_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_neg_right : cov[X, -Y; μ] = -cov[X, Y; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.covariance_smul_right`：covariance_smul_right (c : Real
) : cov[X, c • Y; μ] = c * cov[X, Y; μ]
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma covariance_neg_right : cov[X, -Y; μ] = -cov[X, Y; μ] := by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : ℝ) • Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_right]; simp

@[simp]
/-
**ProbabilityTheory.covariance_fun_neg_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covariance_fun_neg_right : cov[X, fun ω => -Y ω; μ] = -cov[X, Y; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covariance_neg_right`：covariance_neg_right : cov[X, -Y
; μ] = -cov[X, Y; μ]
-/
lemma covariance_fun_neg_right : cov[X, fun ω ↦ -Y ω; μ] = -cov[X, Y; μ] :=
  covariance_neg_right
/-
**ProbabilityTheory.covariance_sub_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covariance_sub_left [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2
 μ) (hZ : MemLp Z 2 μ) : cov[X - Y, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_add_left`：covariance_add_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X + Y, Z; 
μ] = cov[X, Z; μ] + cov[Y, …
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.covariance_neg_left`：covariance_neg_left : cov[-X, Y; 
μ] = -cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X - Y, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_left hX hY.neg hZ, covariance_neg_left]
/-
**ProbabilityTheory.covariance_fun_sub_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covariance_fun_sub_left [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp
 Y 2 μ) (hZ : MemLp Z 2 μ) : cov[fun ω => X ω - Y ω, Z; μ] = cov[X, Z; μ] - cov[
Y, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sub_left`：covariance_sub_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X - Y, Z; 
μ] = cov[X, Z; μ] - cov[Y, …
-/
lemma covariance_fun_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[fun ω ↦ X ω - Y ω, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := covariance_sub_left hX hY hZ
/-
**ProbabilityTheory.covariance_sub_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_sub_right [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 
2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y - Z; μ] = cov[X, Y; μ] - cov[X, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_add_right`：covariance_add_right [IsFiniteMe
asure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y + Z
; μ] = cov[X, Y; μ] + cov[X,…
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.covariance_neg_right`：covariance_neg_right : cov[X, -Y
; μ] = -cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y - Z; μ] = cov[X, Y; μ] - cov[X, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_right hX hY hZ.neg, covariance_neg_right]
/-
**ProbabilityTheory.covariance_fun_sub_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covariance_fun_sub_right [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemL
p Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X, fun ω => Y ω - Z ω; μ] = cov[X, Y; μ] - cov
[X, Z; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sub_right`：covariance_sub_right [IsFiniteMe
asure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y - Z
; μ] = cov[X, Y; μ] - cov[X,…
-/
lemma covariance_fun_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, fun ω ↦ Y ω - Z ω; μ] = cov[X, Y; μ] - cov[X, Z; μ] := covariance_sub_right hX hY hZ
/-
**ProbabilityTheory.covariance_sub_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：covariance_sub_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 
μ) (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) : cov[X - Y, Z - T; μ] = cov[X, Z; μ] -
 cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ；hT : MemLp T 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_sub_left`：covariance_sub_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X - Y, Z; 
μ] = cov[X, Z; μ] - cov[Y, …
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用引理 `ProbabilityTheory.covariance_sub_right`：covariance_sub_right [IsFiniteMe
asure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y - Z
; μ] = cov[X, Y; μ] - cov[X,…
· 使用定理 `_private.Mathlib.Probability.Moments.Covariance.0.ProbabilityTheory.cova
riance_sub_sub._abel_1_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X Y Z T : Ω
 → ℝ} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.covariance X Z μ - Prob
abilit…
-/
lemma covariance_sub_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) :
    cov[X - Y, Z - T; μ] = cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ] := by
  rw [covariance_sub_left hX hY (hZ.sub hT), covariance_sub_right hX hZ hT,
    covariance_sub_right hY hZ hT]
  abel
/-
**ProbabilityTheory.covariance_fun_sub_fun_sub** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_fun_sub_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : Me
mLp Y 2 μ) (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) : cov[fun ω => X ω - Y ω, fun ω
 => Z ω - T ω; μ] = cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ；hZ : MemLp Z 2 μ；hT : MemLp T 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sub_sub`：covariance_sub_sub [IsFiniteMeasur
e μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ)
 : cov[X - Y, Z - T; μ] = …
-/
lemma covariance_fun_sub_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) :
    cov[fun ω ↦ X ω - Y ω, fun ω ↦ Z ω - T ω; μ] =
      cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ] :=
  covariance_sub_sub hX hY hZ hT

@[simp]
/-
**ProbabilityTheory.covariance_sub_const_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_sub_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (
c : Real) : cov[fun ω => X ω - c, Y; μ] = cov[X, Y; μ]
参数：hX : Integrable X μ；c : Real。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_add_const_left`：covariance_add_const_left [
IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) : cov[fun ω => X ω + c,
 Y; μ] = cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_sub_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ X ω - c, Y; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX]

@[simp]
/-
**ProbabilityTheory.covariance_const_sub_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_const_sub_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (
c : Real) : cov[fun ω => c - X ω, Y; μ] = -cov[X, Y; μ]
参数：hX : Integrable X μ；c : Real。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_const_add_left`：covariance_const_add_left [
IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) : cov[fun ω => c + X ω,
 Y; μ] = cov[X, Y; μ]
· 使用定理 `MeasureTheory.Integrable.fun_neg`：∀ {α : Type u_1} {β : Type u_2} {m : M
easurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   
{f : α → β}, MeasureTh…
· 使用引理 `ProbabilityTheory.covariance_fun_neg_left`：covariance_fun_neg_left : cov
[fun ω => -X ω, Y; μ] = -cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_const_sub_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ c - X ω, Y; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX.fun_neg]

@[simp]
/-
**ProbabilityTheory.covariance_sub_const_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_sub_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) 
(c : Real) : cov[X, fun ω => Y ω - c; μ] = cov[X, Y; μ]
参数：hY : Integrable Y μ；c : Real。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_add_const_right`：covariance_add_const_right
 [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) : cov[X, fun ω => Y ω
 + c; μ] = cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_sub_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ Y ω - c; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY]

@[simp]
/-
**ProbabilityTheory.covariance_const_sub_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_const_sub_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) 
(c : Real) : cov[X, fun ω => c - Y ω; μ] = -cov[X, Y; μ]
参数：hY : Integrable Y μ；c : Real。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.covariance_const_add_right`：covariance_const_add_right
 [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) : cov[X, fun ω => c +
 Y ω; μ] = cov[X, Y; μ]
· 使用定理 `MeasureTheory.Integrable.fun_neg`：∀ {α : Type u_1} {β : Type u_2} {m : M
easurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   
{f : α → β}, MeasureTh…
· 使用引理 `ProbabilityTheory.covariance_fun_neg_right`：covariance_fun_neg_right : c
ov[X, fun ω => -Y ω; μ] = -cov[X, Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_const_sub_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ c - Y ω; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY.fun_neg]

section Sum

variable {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} [IsFiniteMeasure μ]

/-
**ProbabilityTheory.covariance_sum_left'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_sum_left' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2
 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i in s, cov[X i, Y; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covariance_zero_left`：∀ {Ω : Type u_1} {mΩ : Measurabl
eSpace Ω} {Y : Ω → ℝ} {μ : MeasureTheory.Measure Ω},   ProbabilityTheory.covaria
nce 0 Y μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `ProbabilityTheory.covariance_add_left`：covariance_add_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X + Y, Z; 
μ] = cov[X, Z; μ] + cov[Y, …
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma covariance_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i ∈ s, X i, Y; μ] = ∑ i ∈ s, cov[X i, Y; μ] := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h_ind =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, covariance_add_left, h_ind]
    · exact fun j hj ↦ hX j (by simp [hj])
    · exact hX i (by simp)
    · exact memLp_finsetSum' s (fun j hj ↦ hX j (by simp [hj]))
    · exact hY
/-
**ProbabilityTheory.covariance_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covariance_sum_left [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : Mem
Lp Y 2 μ) : cov[∑ i, X i, Y; μ] = ∑ i, cov[X i, Y; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sum_left'`：covariance_sum_left' (hX : foral
l i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i i
n s, cov[X i, Y; μ]
-/
lemma covariance_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i, X i, Y; μ] = ∑ i, cov[X i, Y; μ] :=
  covariance_sum_left' (fun _ _ ↦ hX _) hY
/-
**ProbabilityTheory.covariance_fun_sum_left'** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covariance_fun_sum_left' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp
 Y 2 μ) : cov[fun ω => ∑ i in s, X i ω, Y; μ] = ∑ i in s, cov[X i, Y; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
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
· 使用引理 `ProbabilityTheory.covariance_sum_left'`：covariance_sum_left' (hX : foral
l i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i i
n s, cov[X i, Y; μ]
-/
lemma covariance_fun_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω ↦ ∑ i ∈ s, X i ω, Y; μ] = ∑ i ∈ s, cov[X i, Y; μ] := by
  convert! covariance_sum_left' hX hY
  simp
/-
**ProbabilityTheory.covariance_fun_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covariance_fun_sum_left [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY :
 MemLp Y 2 μ) : cov[fun ω => ∑ i, X i ω, Y; μ] = ∑ i, cov[X i, Y; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
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
· 使用引理 `ProbabilityTheory.covariance_sum_left`：covariance_sum_left [Fintype ι] (
hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i, X i, Y; μ] = ∑ i, 
cov[X i, Y; μ]
-/
lemma covariance_fun_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω ↦ ∑ i, X i ω, Y; μ] = ∑ i, cov[X i, Y; μ] := by
  convert! covariance_sum_left hX hY
  simp
/-
**ProbabilityTheory.covariance_sum_right'** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：covariance_sum_right' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 
2 μ) : cov[Y, ∑ i in s, X i; μ] = ∑ i in s, cov[Y, X i; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_comm`：covariance_comm : cov[X, Y; μ] = cov[
Y, X; μ]
· 使用引理 `ProbabilityTheory.covariance_sum_left'`：covariance_sum_left' (hX : foral
l i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i i
n s, cov[X i, Y; μ]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i ∈ s, X i; μ] = ∑ i ∈ s, cov[Y, X i; μ] := by
  rw [covariance_comm, covariance_sum_left' hX hY]
  simp_rw [covariance_comm]
/-
**ProbabilityTheory.covariance_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_sum_right [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : Me
mLp Y 2 μ) : cov[Y, ∑ i, X i; μ] = ∑ i, cov[Y, X i; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sum_right'`：covariance_sum_right' (hX : for
all i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[Y, ∑ i in s, X i; μ] = ∑ i
 in s, cov[Y, X i; μ]
-/
lemma covariance_sum_right [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i, X i; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_sum_right' (fun _ _ ↦ hX _) hY
/-
**ProbabilityTheory.covariance_fun_sum_right'** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covariance_fun_sum_right' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemL
p Y 2 μ) : cov[Y, fun ω => ∑ i in s, X i ω; μ] = ∑ i in s, cov[Y, X i; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
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
· 使用引理 `ProbabilityTheory.covariance_sum_right'`：covariance_sum_right' (hX : for
all i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[Y, ∑ i in s, X i; μ] = ∑ i
 in s, cov[Y, X i; μ]
-/
lemma covariance_fun_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω ↦ ∑ i ∈ s, X i ω; μ] = ∑ i ∈ s, cov[Y, X i; μ] := by
  convert! covariance_sum_right' hX hY
  simp
/-
**ProbabilityTheory.covariance_fun_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covariance_fun_sum_right [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY 
: MemLp Y 2 μ) : cov[Y, fun ω => ∑ i, X i ω; μ] = ∑ i, cov[Y, X i; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_fun_sum_right'`：covariance_fun_sum_right' (
hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[Y, fun ω => ∑ i in
 s, X i ω; μ] = ∑ i in s, cov[Y, …
-/
lemma covariance_fun_sum_right [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω ↦ ∑ i, X i ω; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_fun_sum_right' (fun _ _ ↦ hX _) hY
/-
**ProbabilityTheory.covariance_sum_sum'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covariance_sum_sum' {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'} (hX
 : forall i in s, MemLp (X i) 2 μ) (hY : forall i in t, MemLp (Y i) 2 μ) : cov[∑
 i in s, X i, ∑ j in t, Y j; μ] = ∑ i in s, ∑ j in t, cov[X i, Y j; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : forall i in t, MemLp (Y i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_sum_left'`：covariance_sum_left' (hX : foral
l i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i i
n s, cov[X i, Y; μ]
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ProbabilityTheory.covariance_sum_right'`：covariance_sum_right' (hX : for
all i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[Y, ∑ i in s, X i; μ] = ∑ i
 in s, cov[Y, X i; μ]
-/
lemma covariance_sum_sum' {ι' : Type*} {Y : ι' → Ω → ℝ} {t : Finset ι'}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ i ∈ t, MemLp (Y i) 2 μ) :
    cov[∑ i ∈ s, X i, ∑ j ∈ t, Y j; μ] = ∑ i ∈ s, ∑ j ∈ t, cov[X i, Y j; μ] := by
  rw [covariance_sum_left' hX]
  · exact Finset.sum_congr rfl fun i hi ↦ by rw [covariance_sum_right' hY (hX i hi)]
  · exact memLp_finsetSum' t hY
/-
**ProbabilityTheory.covariance_sum_sum** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> R
eal} (hX : forall i, MemLp (X i) 2 μ) (hY : forall i, MemLp (Y i) 2 μ) : cov[∑ i
, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : forall i, MemLp (Y i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_sum_sum'`：covariance_sum_sum' {ι' : Type*} 
{Y : ι' -> Ω -> Real} {t : Finset ι'} (hX : forall i in s, MemLp (X i) 2 μ) (hY 
: forall i in t, MemLp (Y i…
-/
lemma covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    cov[∑ i, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_sum_sum' (fun _ _ ↦ hX _) (fun _ _ ↦ hY _)
/-
**ProbabilityTheory.covariance_fun_sum_fun_sum'** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：covariance_fun_sum_fun_sum' {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset
 ι'} (hX : forall i in s, MemLp (X i) 2 μ) (hY : forall i in t, MemLp (Y i) 2 μ)
 : cov[fun ω => ∑ i in s, X i ω, fun ω => ∑ j in t, Y j ω; μ] = ∑ i in s, ∑ j in
 t, cov[X i, Y j; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ；hY : forall i in t, MemLp (Y i) 2 μ。
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
· 使用引理 `ProbabilityTheory.covariance_sum_sum'`：covariance_sum_sum' {ι' : Type*} 
{Y : ι' -> Ω -> Real} {t : Finset ι'} (hX : forall i in s, MemLp (X i) 2 μ) (hY 
: forall i in t, MemLp (Y i…
-/
lemma covariance_fun_sum_fun_sum' {ι' : Type*} {Y : ι' → Ω → ℝ} {t : Finset ι'}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ i ∈ t, MemLp (Y i) 2 μ) :
    cov[fun ω ↦ ∑ i ∈ s, X i ω, fun ω ↦ ∑ j ∈ t, Y j ω; μ]
      = ∑ i ∈ s, ∑ j ∈ t, cov[X i, Y j; μ] := by
  convert! covariance_sum_sum' hX hY
  all_goals simp
/-
**ProbabilityTheory.covariance_fun_sum_fun_sum** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covariance_fun_sum_fun_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -
> Ω -> Real} (hX : forall i, MemLp (X i) 2 μ) (hY : forall i, MemLp (Y i) 2 μ) :
 cov[fun ω => ∑ i, X i ω, fun ω => ∑ j, Y j ω; μ] = ∑ i, ∑ j, cov[X i, Y j; μ]
参数：hX : forall i, MemLp (X i) 2 μ；hY : forall i, MemLp (Y i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covariance_fun_sum_fun_sum'`：covariance_fun_sum_fun_su
m' {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'} (hX : forall i in s, MemLp
 (X i) 2 μ) (hY : forall i in t, Me…
-/
lemma covariance_fun_sum_fun_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    cov[fun ω ↦ ∑ i, X i ω, fun ω ↦ ∑ j, Y j ω; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_fun_sum_fun_sum' (fun _ _ ↦ hX _) (fun _ _ ↦ hY _)

end Sum

section Map

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}

/-
**ProbabilityTheory.covariance_map_equiv** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covariance_map_equiv (X Y : Ω -> Real) (Z : Ω' ≃ᵐ Ω) : cov[X, Y; μ.map Z] 
= cov[X ∘ Z, Y ∘ Z; μ]
参数：X Y : Ω -> Real；Z : Ω' ≃ᵐ Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covariance_map_equiv (X Y : Ω → ℝ) (Z : Ω' ≃ᵐ Ω) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, integral_map_equiv, Function.comp_apply]
/-
**ProbabilityTheory.covariance_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：covariance_map {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z)) (hY :
 AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) : cov[X, Y; μ.map Z] 
= cov[X ∘ Z, Y ∘ Z; μ]
参数：hX : AEStronglyMeasurable X (μ.map Z)；hY : AEStronglyMeasurable Y (μ.map Z)；h
Z : AEMeasurable Z μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
lemma covariance_map {Z : Ω' → Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, Function.comp_apply]
  repeat rw [integral_map]
  any_goals assumption
  exact (hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const)
/-
**ProbabilityTheory.covariance_map_fun** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：covariance_map_fun {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z)) (
hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) : cov[X, Y; μ.map
 Z] = cov[fun ω => X (Z ω), fun ω => Y (Z ω); μ]
参数：hX : AEStronglyMeasurable X (μ.map Z)；hY : AEStronglyMeasurable Y (μ.map Z)；h
Z : AEMeasurable Z μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covariance_map`：covariance_map {Z : Ω' -> Ω} (hX : AES
tronglyMeasurable X (μ.map Z)) (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEM
easurable Z μ) : cov[X…
-/
lemma covariance_map_fun {Z : Ω' → Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[fun ω ↦ X (Z ω), fun ω ↦ Y (Z ω); μ] :=
  covariance_map hX hY hZ

end Map

/-
**ProbabilityTheory.IndepFun.covariance_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : MeasureTheory
.Measure Ω},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.MemLp X 2 μ 
→ MeasureTheory.MemLp Y 2 μ → ProbabilityTheory.covariance X Y μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MemLp.isProbabilityMeasure_of_indepFun`：∀ {Ω : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measu
re Ω}   [inst_1 : NormedAddCommGroup E] [i…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ProbabilityTheory.covariance_eq_sub`：covariance_eq_sub [IsProbabilityMea
sure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] *
 μ[Y]
· 使用定理 `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`：∀ {Ω : Type u_1
} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.M
easure Ω} {X Y : Ω → 𝕜},   ProbabilityTheory.…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
-/
lemma IndepFun.covariance_eq_zero (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = 0 := by
   by_cases h' : ∀ᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY, h.integral_mul_eq_mul_integral
       hX.aestronglyMeasurable hY.aestronglyMeasurable, sub_self]

section Prod

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Ω → ℝ} {Y : Ω' → ℝ}

/-
**ProbabilityTheory.covariance_fst_snd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covariance_fst_snd_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) : cov[fun 
p => X p.1, fun p => Y p.2; μ.prod ν] = 0
参数：hfμ : MemLp X 2 μ；hgν : MemLp Y 2 ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.IndepFun.covariance_eq_zero`：∀ {Ω : Type u_1} {mΩ : Me
asurableSpace Ω} {X Y : Ω → ℝ} {μ : MeasureTheory.Measure Ω},   ProbabilityTheor
y.IndepFun X Y μ →     MeasureTheor…
· 使用引理 `ProbabilityTheory.indepFun_prod₀`：indepFun_prod₀ (mX : AEMeasurable X μ)
 (mY : AEMeasurable Y ν) : (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2)
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
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
-/
lemma covariance_fst_snd_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    cov[fun p ↦ X p.1, fun p ↦ Y p.2; μ.prod ν] = 0 :=
  (indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable).covariance_eq_zero
    (hfμ.comp_fst ν) (hgν.comp_snd μ)

end Prod

end ProbabilityTheory

