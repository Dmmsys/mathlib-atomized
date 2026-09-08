/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Domain of the moment-generating function

For `X` a real random variable and `μ` a finite measure, the set
`{t | Integrable (fun ω ↦ exp (t * X ω)) μ}` is an interval containing zero. This is the set of
points for which the moment-generating function `mgf X μ t` is well defined.
We denote that set by `integrableExpSet X μ`.

We prove the integrability of other functions for `t` in the interior of that interval.

## Main definitions

* `ProbabilityTheory.IntegrableExpSet`: the interval of reals for which `exp (t * X)` is integrable.

## Main results

* `ProbabilityTheory.integrable_exp_mul_of_le_of_le`: if `exp (u * X)` is integrable for `u = a` and
  `u = b` then it is integrable on `[a, b]`.
* `ProbabilityTheory.convex_integrableExpSet`: `integrableExpSet X μ` is a convex set.
* `ProbabilityTheory.integrable_exp_mul_of_nonpos_of_ge`: if `exp (u * X)` is integrable for `u ≤ 0`
  then it is integrable on `[u, 0]`.
* `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior`: for `v` in the interior of the
  interval in which `exp (t * X)` is integrable, for all nonnegative `p : ℝ`,
  `|X| ^ p * exp (v * X)` is integrable.
* `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`: if 0 belongs to the interior of
  `integrableExpSet X μ`, then `X` is in `ℒp` for all finite `p`.

-/

@[expose] public section


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ}

section Interval

/-
**ProbabilityTheory.integrable_exp_mul_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：integrable_exp_mul_of_le_of_le {a b : Real} (ha : Integrable (fun ω => exp
 (a * X ω)) μ) (hb : Integrable (fun ω => exp (b * X ω)) μ) (hat : a <= t) (htb 
: t <= b) : Integrable (fun ω => exp (t * X ω)) μ
参数：ha : Integrable (fun ω => exp (a * X ω)) μ；hb : Integrable (fun ω => exp (b *
 X ω)) μ；hat : a <= t；htb : t <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
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
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
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
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp_mul`：aemeasurable_of_aemeasurable_
exp_mul {t : Real} (ht : t != 0) (hf : AEMeasurable (fun x => exp (t * f x)) μ) 
: AEMeasurable f μ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 49 条，此处仅展示前 30 条）
-/
lemma integrable_exp_mul_of_le_of_le {a b : ℝ}
    (ha : Integrable (fun ω ↦ exp (a * X ω)) μ) (hb : Integrable (fun ω ↦ exp (b * X ω)) μ)
    (hat : a ≤ t) (htb : t ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine Integrable.mono (ha.add hb) ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases hab : a = b
    · have ha_eq_t : a = t := le_antisymm hat (hab ▸ htb)
      rw [← ha_eq_t]
      exact ha.1
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine measurable_exp.comp_aemeasurable (AEMeasurable.const_mul ?_ _)
      by_cases ha_zero : a = 0
      · refine aemeasurable_of_aemeasurable_exp_mul ?_ hb.1.aemeasurable
        rw [ha_zero] at hab
        exact Ne.symm hab
      · exact aemeasurable_of_aemeasurable_exp_mul ha_zero ha.1.aemeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (X ω) with h | h
    · calc exp (t * X ω)
      _ ≤ exp (b * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right htb h)
      _ ≤ exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_left (exp_nonneg _)
    · calc exp (t * X ω)
      _ ≤ exp (a * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonpos_right hat h)
      _ ≤ exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_right (exp_nonneg _)

/-- If `ω ↦ exp (u * X ω)` is integrable at `u` and `-u`, then it is integrable on `[-u, u]`. -/
/-
**ProbabilityTheory.integrable_exp_mul_of_abs_le** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：integrable_exp_mul_of_abs_le (hu_int_pos : Integrable (fun ω => exp (u * X
 ω)) μ) (hu_int_neg : Integrable (fun ω => exp (-u * X ω)) μ) (htu : |t| <= |u|)
 : Integrable (fun ω => exp (t * X ω)) μ
参数：hu_int_pos : Integrable (fun ω => exp (u * X ω)) μ；hu_int_neg : Integrable (f
un ω => exp (-u * X ω)) μ；htu : |t| <= |u|。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
If `ω ↦ exp (u * X ω)` is integrable at `u` and `-u`, then it is integrable on `
[-u, u]`.
-/
lemma integrable_exp_mul_of_abs_le
    (hu_int_pos : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω ↦ exp (-u * X ω)) μ)
    (htu : |t| ≤ |u|) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine integrable_exp_mul_of_le_of_le (a := -|u|) (b := |u|) ?_ ?_ ?_ ?_
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · simpa [abs_of_nonpos hu]
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [neg_le]
    exact (neg_le_abs t).trans htu
  · exact (le_abs_self t).trans htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≥ 0`, then it is integrable on `[0, u]`. -/
/-
**ProbabilityTheory.integrable_exp_mul_of_nonneg_of_le** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：integrable_exp_mul_of_nonneg_of_le [IsFiniteMeasure μ] (hu : Integrable (f
un ω => exp (u * X ω)) μ) (h_nonneg : 0 <= t) (htu : t <= u) : Integrable (fun ω
 => exp (t * X ω)) μ
参数：hu : Integrable (fun ω => exp (u * X ω)) μ；h_nonneg : 0 <= t；htu : t <= u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
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
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `ω ↦ exp (u * X ω)` is integrable at `u ≥ 0`, then it is integrable on `[0, u
]`.
-/
lemma integrable_exp_mul_of_nonneg_of_le [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le (by simp) hu h_nonneg htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≤ 0`, then it is integrable on `[u, 0]`. -/
/-
**ProbabilityTheory.integrable_exp_mul_of_nonpos_of_ge** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：integrable_exp_mul_of_nonpos_of_ge [IsFiniteMeasure μ] (hu : Integrable (f
un ω => exp (u * X ω)) μ) (h_nonpos : t <= 0) (htu : u <= t) : Integrable (fun ω
 => exp (t * X ω)) μ
参数：hu : Integrable (fun ω => exp (u * X ω)) μ；h_nonpos : t <= 0；htu : u <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
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
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `ω ↦ exp (u * X ω)` is integrable at `u ≤ 0`, then it is integrable on `[u, 0
]`.
-/
lemma integrable_exp_mul_of_nonpos_of_ge [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonpos : t ≤ 0) (htu : u ≤ t) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le hu (by simp) htu h_nonpos

end Interval

section IntegrableExpSet

/-- The interval of reals `t` for which `exp (t * X)` is integrable. -/
/-
**ProbabilityTheory.integrableExpSet** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：integrableExpSet (X : Ω -> Real) (μ : Measure Ω) : Set Real
参数：X : Ω -> Real；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interval of reals `t` for which `exp (t * X)` is integrable.
-/
def integrableExpSet (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ :=
  {t | Integrable (fun ω ↦ exp (t * X ω)) μ}
/-
**ProbabilityTheory.integrable_of_mem_integrableExpSet** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：integrable_of_mem_integrableExpSet (h : t in integrableExpSet X μ) : Integ
rable (fun ω => exp (t * X ω)) μ
参数：h : t in integrableExpSet X μ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integrable_of_mem_integrableExpSet (h : t ∈ integrableExpSet X μ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := h

/-- `integrableExpSet X μ` is a convex subset of `ℝ` (it is an interval). -/
/-
**ProbabilityTheory.convex_integrableExpSet** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：convex_integrableExpSet : Convex Real (integrableExpSet X μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
`integrableExpSet X μ` is a convex subset of `ℝ` (it is an interval).
-/
lemma convex_integrableExpSet : Convex ℝ (integrableExpSet X μ) := by
  rintro t₁ ht₁ t₂ ht₂ a b ha hb hab
  wlog! h_le : t₁ ≤ t₂
  · rw [add_comm] at hab ⊢
    exact this ht₂ ht₁ hb ha hab h_le.le
  refine integrable_exp_mul_of_le_of_le ht₁ ht₂ ?_ ?_
  · simp only [smul_eq_mul]
    calc t₁
    _ = a * t₁ + b * t₁ := by rw [← add_mul, hab, one_mul]
    _ ≤ a * t₁ + b * t₂ := by gcongr
  · simp only [smul_eq_mul]
    calc a * t₁ + b * t₂
    _ ≤ a * t₂ + b * t₂ := by gcongr
    _ = t₂ := by rw [← add_mul, hab, one_mul]

end IntegrableExpSet

section FiniteMoments

/-
**ProbabilityTheory.aemeasurable_of_integrable_exp_mul** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：aemeasurable_of_integrable_exp_mul (huv : u != v) (hu_int : Integrable (fu
n ω => exp (u * X ω)) μ) (hv_int : Integrable (fun ω => exp (v * X ω)) μ) : AEMe
asurable X μ
参数：huv : u != v；hu_int : Integrable (fun ω => exp (u * X ω)) μ；hv_int : Integrab
le (fun ω => exp (v * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_ne_of_eq`：ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a != b) (h₂
 : b = c) : a != c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp_mul`：aemeasurable_of_aemeasurable_
exp_mul {t : Real} (ht : t != 0) (hf : AEMeasurable (fun x => exp (t * f x)) μ) 
: AEMeasurable f μ
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma aemeasurable_of_integrable_exp_mul (huv : u ≠ v)
    (hu_int : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hv_int : Integrable (fun ω ↦ exp (v * X ω)) μ) :
    AEMeasurable X μ := by
  by_cases hu : u = 0
  · have hv : v ≠ 0 := ne_of_ne_of_eq huv.symm hu
    exact aemeasurable_of_aemeasurable_exp_mul hv hv_int.aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hu hu_int.aemeasurable

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (t * |X| + v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_exp_mul_abs_add** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω => exp ((v + t)
 * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) : Integra
ble (fun ω => exp (t * |X ω| + v * X ω)) μ
参数：ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_neg : Integra
ble (fun ω => exp ((v - t) * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `ProbabilityTheory.aemeasurable_of_integrable_exp_mul`：aemeasurable_of_in
tegrable_exp_mul (huv : u != v) (hu_int : Integrable (fun ω => exp (u * X ω)) μ)
 (hv_int : Integrable (fun ω => exp (v * X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_add`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (t * |X| + v * X)` is integrable.
-/
lemma integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ exp (t * |X ω| + v * X ω)) μ := by
  have h_int_add : Integrable (fun a ↦ exp ((v + t) * X a) + exp ((v - t) * X a)) μ :=
    ht_int_pos.add <| by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add, add_zero] at ht_int_pos ⊢
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
    · fun_prop
    · rw [← sub_ne_zero]
      simp [ht]
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    -- ⊢ exp (t * |X ω| + v * X ω) ≤ exp ((v + t) * X ω) + exp ((v - t) * X ω)
    rcases le_total 0 (X ω) with h_nonneg | h_nonpos
    · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
      positivity
    · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
        ← sub_eq_add_neg, le_add_iff_nonneg_left]
      positivity

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (t * |X ω|)` is
integrable. -/
/-
**ProbabilityTheory.integrable_exp_mul_abs** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ
) (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) : Integrable (fun ω => e
xp (t * |X ω|)) μ
参数：ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : Integrable (f
un ω => exp (-t * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_exp_mul_abs_add`：integrable_exp_mul_abs_add
 (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integr
able (fun ω => exp ((v - t) * X ω)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (t * |X ω|)`
 is
integrable.
-/
lemma integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) :
    Integrable (fun ω ↦ exp (t * |X ω|)) μ := by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (|t| * |X| + v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_exp_abs_mul_abs_add** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω => exp ((v 
+ t) * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) : Int
egrable (fun ω => exp (|t| * |X ω| + v * X ω)) μ
参数：ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_neg : Integra
ble (fun ω => exp ((v - t) * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `ProbabilityTheory.integrable_exp_mul_abs_add`：integrable_exp_mul_abs_add
 (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integr
able (fun ω => exp ((v - t) * X ω)…
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (|t| * |X| + v * X)` is integrable.
-/
lemma integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ exp (|t| * |X ω| + v * X ω)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (|t| * |X ω|)` is
integrable. -/
/-
**ProbabilityTheory.integrable_exp_abs_mul_abs** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω => exp (t * X ω
)) μ) (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) : Integrable (fun ω 
=> exp (|t| * |X ω|)) μ
参数：ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : Integrable (f
un ω => exp (-t * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `ProbabilityTheory.integrable_exp_mul_abs`：integrable_exp_mul_abs (ht_int
_pos : Integrable (fun ω => exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω =>
 exp (-t * X ω)) μ) : Integrab…
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (|t| * |X ω|
)` is
integrable.
-/
lemma integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) :
    Integrable (fun ω ↦ exp (|t| * |X ω|)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

/-- Auxiliary lemma for `rpow_abs_le_mul_max_exp`. -/
/-
**ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：rpow_abs_le_mul_max_exp_of_pos (x : Real) {t p : Real} (hp : 0 <= p) (ht :
 0 < t) : |x| ^ p <= (p / t) ^ p * max (exp (t * x)) (exp (-t * x))
参数：x : Real；hp : 0 <= p；ht : 0 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `Real.le_inv_mul_exp`：le_inv_mul_exp (x : Real) {c : Real} (hc : 0 < c) :
 x <= c⁻¹ * exp (c * x)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `rpow_abs_le_mul_max_exp`.
-/
lemma rpow_abs_le_mul_max_exp_of_pos (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : 0 < t) :
    |x| ^ p ≤ (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, rpow_zero, zero_div, neg_mul, one_mul, le_sup_iff, one_le_exp_iff,
      Left.nonneg_neg_iff]
    exact le_total 0 (t * x)
  have h_x_le c (hc : 0 < c) : x ≤ c⁻¹ * exp (c * x) := le_inv_mul_exp x hc
  have h_neg_x_le c (hc : 0 < c) : -x ≤ c⁻¹ * exp (-c * x) := by simpa using le_inv_mul_exp (-x) hc
  have h_abs_le c (hc : 0 < c) : |x| ≤ c⁻¹ * max (exp (c * x)) (exp (-c * x)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · rw [neg_le]
      refine (h_neg_x_le c hc).trans ?_
      gcongr
      exact le_max_right _ _
    · refine (h_x_le c hc).trans ?_
      gcongr
      exact le_max_left _ _
  calc |x| ^ p
  _ ≤ ((t / p)⁻¹ * max (exp (t / p * x)) (exp (-t / p * x))) ^ p := by
    gcongr
    convert! h_abs_le (t / p) (div_pos ht (hp.lt_of_ne' hp_zero)) using 5
    rw [neg_div]
  _ = (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
    rw [mul_rpow (by positivity) (by positivity)]
    congr
    · simp
    · rw [rpow_max (by positivity) (by positivity) hp, ← exp_mul, ← exp_mul]
      ring_nf
      congr <;> rw [mul_assoc, mul_inv_cancel₀ hp_zero, mul_one]
/-
**ProbabilityTheory.rpow_abs_le_mul_max_exp** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：rpow_abs_le_mul_max_exp (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0
) : |x| ^ p <= (p / |t|) ^ p * max (exp (t * x)) (exp (-t * x))
参数：x : Real；hp : 0 <= p；ht : t != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos`：rpow_abs_le_mul_max_ex
p_of_pos (x : Real) {t p : Real} (hp : 0 <= p) (ht : 0 < t) : |x| ^ p <= (p / t)
 ^ p * max (exp (t * x)) (exp (-t * x)…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
lemma rpow_abs_le_mul_max_exp (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : t ≠ 0) :
    |x| ^ p ≤ (p / |t|) ^ p * max (exp (t * x)) (exp (-t * x)) := by
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · rw [abs_of_nonpos ht_neg.le, sup_comm]
    convert! rpow_abs_le_mul_max_exp_of_pos x hp (t := -t) (by simp [ht_neg])
    simp
  · rw [abs_of_nonneg ht_pos.le]
    exact rpow_abs_le_mul_max_exp_of_pos x hp ht_pos
/-
**ProbabilityTheory.rpow_abs_le_mul_exp_abs** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：rpow_abs_le_mul_exp_abs (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0
) : |x| ^ p <= (p / |t|) ^ p * exp (|t| * |x|)
参数：x : Real；hp : 0 <= p；ht : t != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos`：rpow_abs_le_mul_max_ex
p_of_pos (x : Real) {t p : Real} (hp : 0 <= p) (ht : 0 < t) : |x| ^ p <= (p / t)
 ^ p * max (exp (t * x)) (exp (-t * x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.Positivity.abs_pos_of_ne_zero`：abs_pos_of_ne_zero {α : Type
*} [AddGroup α] [LinearOrder α] [AddLeftMono α] {a : α} : a != 0 -> 0 < |a|
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma rpow_abs_le_mul_exp_abs (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : t ≠ 0) :
    |x| ^ p ≤ (p / |t|) ^ p * exp (|t| * |x|) := by
  refine (rpow_abs_le_mul_max_exp_of_pos x hp (t := |t|) ?_).trans_eq ?_
  · simp [ht]
  · congr
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      simp only [neg_mul, sup_eq_left, exp_le_exp, neg_le_self_iff]
      positivity
    · rw [abs_of_nonpos hx]
      simp only [neg_mul, mul_neg, sup_eq_right, exp_le_exp, le_neg_self_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hx

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ` and any `x ∈ [0, |t|)`,
`|X| ^ p * exp (v * X + x * |X|)` is integrable. -/
/-
**ProbabilityTheory.integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul** 是 Ma
thlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : Real} (h_int_po
s : Integrable (fun ω => exp ((v + t) * X ω)) μ) (h_int_neg : Integrable (fun ω 
=> exp ((v - t) * X ω)) μ) (h_nonneg : 0 <= x) (hx : x < |t|) {p : Real} (hp : 0
 <= p) : Integrable (fun a => |X a| ^ p * exp (v * X a + x * |X a|)) μ
参数：h_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；h_int_neg : Integrabl
e (fun ω => exp ((v - t) * X ω)) μ；h_nonneg : 0 <= x；hx : x < |t|；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `ProbabilityTheory.aemeasurable_of_integrable_exp_mul`：aemeasurable_of_in
tegrable_exp_mul (huv : u != v) (hu_int : Integrable (fun ω => exp (u * X ω)) μ)
 (hv_int : Integrable (fun ω => exp (v * X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `Continuous.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ` and any `x ∈ [0, |t|)`,
`|X| ^ p * exp (v * X + x * |X|)` is integrable.
-/
lemma integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : ℝ}
    (h_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (h_nonneg : 0 ≤ x) (hx : x < |t|)
    {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun a ↦ |X a| ^ p * exp (v * X a + x * |X a|)) μ := by
  have ht : t ≠ 0 := by
    suffices |t| ≠ 0 by simpa
    exact (h_nonneg.trans_lt hx).ne'
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_eq_abs, abs_exp]
  have h_le a : |X a| ^ p * exp (v * X a + x * |X a|)
      ≤ (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|) := by
    simp_rw [exp_add, mul_comm (exp (v * X a)), ← mul_assoc]
    gcongr ?_ * _
    have : |t| = |t| - x + x := by simp
    nth_rw 2 [this]
    rw [add_mul, exp_add, ← mul_assoc]
    gcongr ?_ * _
    convert! rpow_abs_le_mul_exp_abs (X a) hp (t := |t| - x) _ using 4
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · rw [sub_ne_zero]
      exact hx.ne'
  refine Integrable.mono (g := fun a ↦ (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|))
    ?_ ?_ <| ae_of_all _ fun ω ↦ ?_
  · refine Integrable.const_mul ?_ _
    simp_rw [add_comm (v * X _)]
    exact integrable_exp_abs_mul_abs_add h_int_pos h_int_neg
  · fun_prop
  · simp only [norm_mul, norm_eq_abs, abs_exp]
    simp_rw [abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    refine (h_le ω).trans_eq ?_
    congr
    symm
    simp only [abs_eq_self]
    positivity [sub_nonneg_of_le hx.le]

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for any `n : ℕ` and any `x ∈ [0, |t|)`,
`|X| ^ n * exp (v * X + x * |X|)` is integrable. -/
/-
**ProbabilityTheory.integrable_pow_abs_mul_exp_add_of_integrable_exp_mul** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_mul_exp_add_of_integrable_exp_mul {x : Real} (h_int_pos
 : Integrable (fun ω => exp ((v + t) * X ω)) μ) (h_int_neg : Integrable (fun ω =
> exp ((v - t) * X ω)) μ) (h_nonneg : 0 <= x) (hx : x < |t|) (n : Nat) : Integra
ble (fun a => |X a| ^ n * exp (v * X a + x * |X a|)) μ
参数：h_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；h_int_neg : Integrabl
e (fun ω => exp ((v - t) * X ω)) μ；h_nonneg : 0 <= x；hx : x < |t|；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul`
：integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : Real} (h_int_pos : I
ntegrable (fun ω => exp ((v + t) * X ω)) μ) (h_int_neg : Inte…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for any `n : ℕ` and any `x ∈ [0, |t|)`,
`|X| ^ n * exp (v * X + x * |X|)` is integrable.
-/
lemma integrable_pow_abs_mul_exp_add_of_integrable_exp_mul {x : ℝ}
    (h_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (h_nonneg : 0 ≤ x) (hx : x < |t|)
    (n : ℕ) :
    Integrable (fun a ↦ |X a| ^ n * exp (v * X a + x * |X a|)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg h_nonneg hx
      n.cast_nonneg
  simp

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ`, `|X| ^ p * exp (v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_rpow_abs_mul_exp_of_integrable_exp_mul** 是 Mathli
b 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_po
s : Integrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integrable (fun ω
 => exp ((v - t) * X ω)) μ) {p : Real} (hp : 0 <= p) : Integrable (fun ω => |X ω
| ^ p * exp (v * X ω)) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_n
eg : Integrable (fun ω => exp ((v - t) * X ω)) μ；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul`
：integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : Real} (h_int_pos : I
ntegrable (fun ω => exp ((v + t) * X ω)) μ) (h_int_neg : Inte…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ`, `|X| ^ p * exp (v * X)` is integrable.
-/
lemma integrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul ht_int_pos ht_int_neg le_rfl _ hp using 4
  · simp
  · simp [ht]

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n : ℕ`,
`|X| ^ n * exp (v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_pow_abs_mul_exp_of_integrable_exp_mul** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos
 : Integrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integrable (fun ω 
=> exp ((v - t) * X ω)) μ) (n : Nat) : Integrable (fun ω => |X ω| ^ n * exp (v *
 X ω)) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_n
eg : Integrable (fun ω => exp ((v - t) * X ω)) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_integrable_exp_mul`：int
egrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integ
rable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Int…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n :
 ℕ`,
`|X| ^ n * exp (v * X)` is integrable.
-/
lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 ≤ (n : ℝ)) with
    ω
  simp

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all nonnegative `p : ℝ`,
`X ^ p * exp (v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : 
Integrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integrable (fun ω => 
exp ((v - t) * X ω)) μ) {p : Real} (hp : 0 <= p) : Integrable (fun ω => X ω ^ p 
* exp (v * X ω)) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_n
eg : Integrable (fun ω => exp ((v - t) * X ω)) μ；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_integrable_exp_mul`：aemeasurable_of_in
tegrable_exp_mul (huv : u != v) (hu_int : Integrable (fun ω => exp (u * X ω)) μ)
 (hv_int : Integrable (fun ω => exp (v * X…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_integrable_exp_mul`：int
egrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integ
rable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Int…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all nonn
egative `p : ℝ`,
`X ^ p * exp (v * X)` is integrable.
-/
lemma integrable_rpow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p * exp (v * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_exp]
    have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg hp
    refine h.mono' ?_ ?_
    · fun_prop
    · refine ae_of_all _ fun ω ↦ ?_
      simp only [norm_mul, norm_eq_abs, abs_abs, abs_exp]
      gcongr
      exact abs_rpow_le_abs_rpow _ _
  · fun_prop

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n : ℕ`,
`X ^ n * exp (v * X)` is integrable. -/
/-
**ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : I
ntegrable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integrable (fun ω => e
xp ((v - t) * X ω)) μ) (n : Nat) : Integrable (fun ω => X ω ^ n * exp (v * X ω))
 μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ；ht_int_n
eg : Integrable (fun ω => exp ((v - t) * X ω)) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul`：integra
ble_rpow_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrable (f
un ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integra…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n :
 ℕ`,
`X ^ n * exp (v * X)` is integrable.
-/
lemma integrable_pow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 ≤ (n : ℝ)) with
    ω
  simp

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ p` is
integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Inte
grable (fun ω => exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp (-t * 
X ω)) μ) {p : Real} (hp : 0 <= p) : Integrable (fun ω => |X ω| ^ p) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : I
ntegrable (fun ω => exp (-t * X ω)) μ；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_integrable_exp_mul`：int
egrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integ
rable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Int…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω
| ^ p` is
integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p) μ := by
  have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ n` is
integrable for all `n : ℕ`. That is, all moments of `X` are finite. -/
/-
**ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integ
rable (fun ω => exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp (-t * X
 ω)) μ) (n : Nat) : Integrable (fun ω => |X ω| ^ n) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : I
ntegrable (fun ω => exp (-t * X ω)) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul`：integrable_
rpow_abs_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrable (fun ω => 
exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω
| ^ n` is
integrable for all `n : ℕ`. That is, all moments of `X` are finite.
-/
lemma integrable_pow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  convert!
    integrable_rpow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 ≤ (n : ℝ)) with
    ω
  simp

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ p` is
integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_of_integrable_exp_mul** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrab
le (fun ω => exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp (-t * X ω)
) μ) {p : Real} (hp : 0 <= p) : Integrable (fun ω => X ω ^ p) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : I
ntegrable (fun ω => exp (-t * X ω)) μ；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul`：integra
ble_rpow_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrable (f
un ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integra…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω 
^ p` is
integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p) μ := by
  have h := integrable_rpow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ n` is
integrable for all `n : ℕ`. -/
/-
**ProbabilityTheory.integrable_pow_of_integrable_exp_mul** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrabl
e (fun ω => exp (t * X ω)) μ) (ht_int_neg : Integrable (fun ω => exp (-t * X ω))
 μ) (n : Nat) : Integrable (fun ω => X ω ^ n) μ
参数：ht : t != 0；ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ；ht_int_neg : I
ntegrable (fun ω => exp (-t * X ω)) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_of_integrable_exp_mul`：integrable_rpow
_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrable (fun ω => exp (t *
 X ω)) μ) (ht_int_neg : Integrable (fun ω => …
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω 
^ n` is
integrable for all `n : ℕ`.
-/
lemma integrable_pow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (-t * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  convert!
    integrable_rpow_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 ≤ (n : ℝ)) with
    ω
  simp

section IntegrableExpSet

/-
**ProbabilityTheory.add_half_inf_sub_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：add_half_inf_sub_mem_Ioo {l u v : Real} (hv : v in Set.Ioo l u) : v + ((v 
- l) ⊓ (u - v)) / 2 in Set.Ioo l u
参数：hv : v in Set.Ioo l u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 35 条，此处仅展示前 30 条）
-/
lemma add_half_inf_sub_mem_Ioo {l u v : ℝ} (hv : v ∈ Set.Ioo l u) :
    v + ((v - l) ⊓ (u - v)) / 2 ∈ Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l < v := hv.1
    _ ≤ v + ((v - l) ⊓ (u - v)) / 2 := le_add_of_nonneg_right (by positivity)
  · calc v + ((v - l) ⊓ (u - v)) / 2
    _ < v + ((v - l) ⊓ (u - v)) := by gcongr; exact half_lt_self (by positivity)
    _ ≤ v + (u - v) := by gcongr; exact inf_le_right
    _ = u := by abel
/-
**ProbabilityTheory.sub_half_inf_sub_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：sub_half_inf_sub_mem_Ioo {l u v : Real} (hv : v in Set.Ioo l u) : v - ((v 
- l) ⊓ (u - v)) / 2 in Set.Ioo l u
参数：hv : v in Set.Ioo l u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Probability.Moments.IntegrableExpMul.0.ProbabilityTheor
y.sub_half_inf_sub_mem_Ioo._abel_1_1`：∀ {l v : ℝ}, l = v - (v - l)
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
（共 35 条，此处仅展示前 30 条）
-/
lemma sub_half_inf_sub_mem_Ioo {l u v : ℝ} (hv : v ∈ Set.Ioo l u) :
    v - ((v - l) ⊓ (u - v)) / 2 ∈ Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l = v - (v - l) := by abel
    _ ≤ v - ((v - l) ⊓ (u - v)) := by gcongr; exact inf_le_left
    _ < v - ((v - l) ⊓ (u - v)) / 2 := by gcongr; exact half_lt_self (by positivity)
  · calc v - ((v - l) ⊓ (u - v)) / 2
    _ ≤ v := by
      rw [sub_le_iff_le_add]
      exact le_add_of_nonneg_right (by positivity)
    _ < u := hv.2

/-- If the interior of the interval `integrableExpSet X μ` is nonempty,
then `X` is a.e. measurable. -/
/-
**ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：aemeasurable_of_mem_interior_integrableExpSet (hv : v in interior (integra
bleExpSet X μ)) : AEMeasurable X μ
参数：hv : v in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If the interior of the interval `integrableExpSet X μ` is nonempty,
then `X` is a.e. measurable.
-/
lemma aemeasurable_of_mem_interior_integrableExpSet (hv : v ∈ interior (integrableExpSet X μ)) :
    AEMeasurable X μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  let t := ((v - l) ⊓ (u - v)) / 2
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  have ht : 0 < t := half_pos h_pos
  by_cases hvt : v + t = 0
  · have hvt' : v - t ≠ 0 := by
      rw [sub_ne_zero]
      refine fun h_eq ↦ ht.ne' ?_
      simpa [h_eq] using hvt
    exact aemeasurable_of_aemeasurable_exp_mul hvt'
      (h_subset (sub_half_inf_sub_mem_Ioo hvlu)).aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hvt
      (h_subset (add_half_inf_sub_mem_Ioo hvlu)).aemeasurable

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in in
terior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω => |
X ω| ^ p * exp (v * X ω)) μ
参数：hv : v in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_integrable_exp_mul`：int
egrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integ
rable (fun ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Int…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_abs_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n * exp (v * X)` is integrable for all `n : ℕ`. -/
/-
**ProbabilityTheory.integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet*
* 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in int
erior (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => |X ω| ^ n * exp (
v * X ω)) μ
参数：hv : v in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior_integrable
ExpSet`：integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in 
interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrab…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n * exp (v * X)` is integrable for all `n : ℕ`.
-/
lemma integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hv
      (by positivity : 0 ≤ (n : ℝ)) with
    ω
  simp

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_mul_exp_of_mem_interior_integrableExpSet** 是
 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_mul_exp_of_mem_interior_integrableExpSet (hv : v in interi
or (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω => X ω ^
 p * exp (v * X ω)) μ
参数：hv : v in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul`：integra
ble_rpow_mul_exp_of_integrable_exp_mul (ht : t != 0) (ht_int_pos : Integrable (f
un ω => exp ((v + t) * X ω)) μ) (ht_int_neg : Integra…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n * exp (v * X)` is integrable for all `n : ℕ`. -/
/-
**ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet** 是 
Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hv : v in interio
r (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => X ω ^ n * exp (v * X 
ω)) μ
参数：hv : v in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_exp_of_mem_interior_integrableExpS
et`：integrable_rpow_mul_exp_of_mem_interior_integrableExpSet (hv : v in interior
 (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n * exp (v * X)` is integrable for all `n : ℕ`.
-/
lemma integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_mul_exp_of_mem_interior_integrableExpSet hv (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_abs_of_mem_interior_integrableExpSet** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_of_mem_interior_integrableExpSet (h : 0 in interior (i
ntegrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω => |X ω| ^ p)
 μ
参数：h : 0 in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior_integrable
ExpSet`：integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in 
interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrab…

--- 原说明 ---
If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_abs_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p) μ := by
  convert! integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all `n : ℕ`. -/
/-
**ProbabilityTheory.integrable_pow_abs_of_mem_interior_integrableExpSet** 是 Math
lib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_of_mem_interior_integrableExpSet (h : 0 in interior (in
tegrableExpSet X μ)) (n : Nat) : Integrable (fun ω => |X ω| ^ n) μ
参数：h : 0 in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_pow_abs_mul_exp_of_mem_interior_integrableE
xpSet`：integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in in
terior (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => |X …

--- 原说明 ---
If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all `n : ℕ`.
-/
lemma integrable_pow_abs_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  convert! integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all nonnegative `p : ℝ`. -/
/-
**ProbabilityTheory.integrable_rpow_of_mem_interior_integrableExpSet** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_of_mem_interior_integrableExpSet (h : 0 in interior (integ
rableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω => X ω ^ p) μ
参数：h : 0 in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_exp_of_mem_interior_integrableExpS
et`：integrable_rpow_mul_exp_of_mem_interior_integrableExpSet (hv : v in interior
 (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (…

--- 原说明 ---
If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all nonnegative `p : ℝ`.
-/
lemma integrable_rpow_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p) μ := by
  convert! integrable_rpow_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all `n : ℕ`. -/
/-
**ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_of_mem_interior_integrableExpSet (h : 0 in interior (integr
ableExpSet X μ)) (n : Nat) : Integrable (fun ω => X ω ^ n) μ
参数：h : 0 in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSe
t`：integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hv : v in interior (
integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => X ω ^ n…

--- 原说明 ---
If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all `n : ℕ`.
-/
lemma integrable_pow_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/-- If 0 belongs to the interior of `integrableExpSet X μ`, then `X` is in `ℒp` for all
finite `p`. -/
/-
**ProbabilityTheory.memLp_of_mem_interior_integrableExpSet** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：memLp_of_mem_interior_integrableExpSet (h : 0 in interior (integrableExpSe
t X μ)) (p : Real>=0) : MemLp X p μ
参数：h : 0 in interior (integrableExpSet X μ)；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.integrable_norm_rpow_iff`：integrable_norm_rpow_iff {f : α 
-> β} {p : Real>=0∞} (hf : AEStronglyMeasurable f μ) (p_zero : p != 0) (p_top : 
p != ∞) : Integrable (fun x …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_of_mem_interior_integrableExpSet`：
integrable_rpow_abs_of_mem_interior_integrableExpSet (h : 0 in interior (integra
bleExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If 0 belongs to the interior of `integrableExpSet X μ`, then `X` is in `ℒp` for 
all
finite `p`.
-/
lemma memLp_of_mem_interior_integrableExpSet (h : 0 ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet h
  by_cases hp_zero : p = 0
  · simp only [hp_zero, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hX.aestronglyMeasurable (mod_cast hp_zero) (by simp)]
  simp only [norm_eq_abs, ENNReal.coe_toReal]
  exact integrable_rpow_abs_of_mem_interior_integrableExpSet h p.2

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`, then `X` is integrable. -/
/-
**ProbabilityTheory.integrable_of_mem_interior_integrableExpSet** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_of_mem_interior_integrableExpSet (h : 0 in interior (integrable
ExpSet X μ)) : Integrable X μ
参数：h : 0 in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet`：integ
rable_pow_of_mem_interior_integrableExpSet (h : 0 in interior (integrableExpSet 
X μ)) (n : Nat) : Integrable (fun ω => X ω ^ n) μ

--- 原说明 ---
If 0 belongs to the interior of the interval `integrableExpSet X μ`, then `X` is
 integrable.
-/
lemma integrable_of_mem_interior_integrableExpSet (h : 0 ∈ interior (integrableExpSet X μ)) :
    Integrable X μ := by
  simpa using integrable_pow_of_mem_interior_integrableExpSet h 1

section Complex

open Complex

variable {z : ℂ}

/-
**ProbabilityTheory.integrable_cexp_mul_of_re_mem_integrableExpSet** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_cexp_mul_of_re_mem_integrableExpSet (hX : AEMeasurable X μ) (hz
 : z.re in integrableExpSet X μ) : Integrable (fun ω => cexp (z * X ω)) μ
参数：hX : AEMeasurable X μ；hz : z.re in integrableExpSet X μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma integrable_cexp_mul_of_re_mem_integrableExpSet (hX : AEMeasurable X μ)
    (hz : z.re ∈ integrableExpSet X μ) :
    Integrable (fun ω ↦ cexp (z * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simpa [Complex.norm_exp] using! hz
  · fun_prop
/-
**ProbabilityTheory.integrable_cexp_mul_of_re_mem_interior_integrableExpSet** 是 
Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_cexp_mul_of_re_mem_interior_integrableExpSet (hz : z.re in inte
rior (integrableExpSet X μ)) : Integrable (fun ω => cexp (z * X ω)) μ
参数：hz : z.re in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_cexp_mul_of_re_mem_integrableExpSet`：integr
able_cexp_mul_of_re_mem_integrableExpSet (hX : AEMeasurable X μ) (hz : z.re in i
ntegrableExpSet X μ) : Integrable (fun ω => cexp (z * …
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
lemma integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) :
    Integrable (fun ω ↦ cexp (z * X ω)) μ :=
  integrable_cexp_mul_of_re_mem_integrableExpSet
    (aemeasurable_of_mem_interior_integrableExpSet hz) (interior_subset hz)
/-
**ProbabilityTheory.integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableEx
pSet** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.r
e in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun
 ω => (|X ω| ^ p : Real) * cexp (z * X ω)) μ
参数：hz : z.re in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
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
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `Continuous.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 37 条，此处仅展示前 30 条）
-/
lemma integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ (|X ω| ^ p : ℝ) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simpa [abs_rpow_of_nonneg (abs_nonneg _), Complex.norm_exp]
    using integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp
/-
**ProbabilityTheory.integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExp
Set** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.re
 in interior (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => |X ω| ^ n 
* cexp (z * X ω)) μ
参数：hz : z.re in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_cexp_of_re_mem_interior_integr
ableExpSet`：integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet (hz
 : z.re in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : I…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * cexp (z * X ω)) μ := by
  convert! integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp
/-
**ProbabilityTheory.integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.re in
 interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrable (fun ω =
> (X ω ^ p : Real) * cexp (z * X ω)) μ
参数：hz : z.re in interior (integrableExpSet X μ)；hp : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
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
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
（共 47 条，此处仅展示前 30 条）
-/
lemma integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ (X ω ^ p : ℝ) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  refine (integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp).mono ?_ ?_
  · fun_prop
  refine ae_of_all _ fun ω ↦ ?_
  simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
  gcongr
  exact abs_rpow_le_abs_rpow _ _
/-
**ProbabilityTheory.integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet*
* 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.re in 
interior (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => X ω ^ n * cexp
 (z * X ω)) μ
参数：hz : z.re in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integrable_rpow_mul_cexp_of_re_mem_interior_integrable
ExpSet`：integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.re 
in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integ…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * cexp (z * X ω)) μ := by
  convert! integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

end Complex

end IntegrableExpSet

end FiniteMoments

end ProbabilityTheory

