/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.Moments.Variance

/-!
# Conditional variance

This file defines the variance of a real-valued random variable conditional to a sigma-algebra.

## TODO

Define the Lebesgue conditional variance. See
[GibbsMeasure](https://github.com/james18lpc/GibbsMeasure) for a definition of the Lebesgue
conditional expectation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory
variable {Ω : Type*} {m₀ m m' : MeasurableSpace Ω} {hm : m ≤ m₀} {X Y : Ω → ℝ} {μ : Measure[m₀] Ω}
  {s : Set Ω}

variable (m X μ) in
/-- Conditional variance of a real-valued random variable. It is defined as `0` if any one of the
following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `μ` is not σ-finite with respect to `m`,
- `X - μ[X | m]` is not square-integrable. -/
/-
**ProbabilityTheory.condVar** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：condVar : Ω -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional variance of a real-valued random variable. It is defined as `0` if a
ny one of the
following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `μ` is not σ-finite with respect to `m`,
- `X - μ[X | m]` is not square-integrable.
-/
noncomputable def condVar : Ω → ℝ := μ[(X - μ[X | m]) ^ 2 | m]

@[inherit_doc] scoped notation "Var[" X "; " μ " | " m "]" => condVar m X μ

/-- Conditional variance of a real-valued random variable. It is defined as `0` if any one of the
following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `volume` is not σ-finite with respect to `m`,
- `X - 𝔼[X | m]` is not square-integrable. -/
scoped notation "Var[" f "|" m "]" => Var[f; MeasureTheory.volume | m]

/-
**ProbabilityTheory.condVar_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：condVar_of_not_le (hm : ¬m <= m₀) : Var[X; μ | m] = 0
参数：hm : ¬m <= m₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condVar.eq_1`：∀ {Ω : Type u_1} {m₀ : MeasurableSpace Ω
} (m : MeasurableSpace Ω) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   Probabili
tyTheory.condVar m X…
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
lemma condVar_of_not_le (hm : ¬m ≤ m₀) : Var[X; μ | m] = 0 := by rw [condVar, condExp_of_not_le hm]
/-
**ProbabilityTheory.condVar_of_not_sigmaFinite** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：condVar_of_not_sigmaFinite (hμm : ¬SigmaFinite (μ.trim hm)) : Var[X; μ | m
] = 0
参数：hμm : ¬SigmaFinite (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condVar.eq_1`：∀ {Ω : Type u_1} {m₀ : MeasurableSpace Ω
} (m : MeasurableSpace Ω) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   Probabili
tyTheory.condVar m X…
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
-/
lemma condVar_of_not_sigmaFinite (hμm : ¬SigmaFinite (μ.trim hm)) :
    Var[X; μ | m] = 0 := by rw [condVar, condExp_of_not_sigmaFinite hm hμm]

open scoped Classical in
/-
**ProbabilityTheory.condVar_of_sigmaFinite** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：condVar_of_sigmaFinite [SigmaFinite (μ.trim hm)] : Var[X; μ | m] = if Inte
grable (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ then if StronglyMeasurable[m] (fun 
ω => (X ω - (μ[X | m]) ω) ^ 2) then fun ω => (X ω - (μ[X | m]) ω) ^ 2 else aestr
onglyMeasurable_condExpL1.mk (condExpL1 hm μ fun ω => (X ω - (μ[X | m]) ω) ^ 2) 
else 0
参数：μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_sigmaFinite`：condExp_of_sigmaFinite (hm : m <= 
m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[f | m] = if Integrable f μ then if Stron
glyMeasurable[m] f then f …
-/
lemma condVar_of_sigmaFinite [SigmaFinite (μ.trim hm)] :
    Var[X; μ | m] =
      if Integrable (fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2) μ then
        if StronglyMeasurable[m] (fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2) then
          fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2
        else aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2)
      else 0 := condExp_of_sigmaFinite _
/-
**ProbabilityTheory.condVar_of_stronglyMeasurable** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：condVar_of_stronglyMeasurable [SigmaFinite (μ.trim hm)] (hX : StronglyMeas
urable[m] X) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) : Var[X; μ | m] = fun ω
 => (X ω - (μ[X | m]) ω) ^ 2
参数：μ.trim hm；hX : StronglyMeasurable[m] X；hXint : Integrable ((X - μ[X | m]) ^ 2
) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.StronglyMeasurable.pow`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Monoid 
β]   [ContinuousMul β], Me…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
-/
lemma condVar_of_stronglyMeasurable [SigmaFinite (μ.trim hm)]
    (hX : StronglyMeasurable[m] X) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) :
    Var[X; μ | m] = fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2 :=
  condExp_of_stronglyMeasurable _ ((hX.sub stronglyMeasurable_condExp).pow _) hXint
/-
**ProbabilityTheory.condVar_of_not_integrable** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：condVar_of_not_integrable (hXint : ¬ Integrable (fun ω => (X ω - (μ[X | m]
) ω) ^ 2) μ) : Var[X; μ | m] = 0
参数：hXint : ¬ Integrable (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
-/
lemma condVar_of_not_integrable (hXint : ¬ Integrable (fun ω ↦ (X ω - (μ[X | m]) ω) ^ 2) μ) :
    Var[X; μ | m] = 0 := condExp_of_not_integrable hXint
/-
**ProbabilityTheory.condVar_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {m₀ m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω},
 ProbabilityTheory.condVar m 0 μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma condVar_zero : Var[0; μ | m] = 0 := by simp [condVar]

@[simp]
/-
**ProbabilityTheory.condVar_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condVar_const (hm : m <= m₀) (c : Real) : Var[fun _ => c; μ | m] = 0
参数：hm : m <= m₀；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condVar_zero`：∀ {Ω : Type u_1} {m₀ m : MeasurableSpace
 Ω} {μ : MeasureTheory.Measure Ω}, ProbabilityTheory.condVar m 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_const`：condExp_const (hm : m <= m₀) (c : E) [IsFin
iteMeasure μ] : μ[fun _ : α => c | m] = fun _ => c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用引理 `MeasureTheory.integrable_const_iff_isFiniteMeasure`：integrable_const_iff
_isFiniteMeasure {c : β} (hc : c != 0) : Integrable (fun _ => c) μ ↔ IsFiniteMea
sure μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
lemma condVar_const (hm : m ≤ m₀) (c : ℝ) : Var[fun _ ↦ c; μ | m] = 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [← Pi.zero_def]
  by_cases hμm : IsFiniteMeasure μ
  · simp [condVar, hm]
  · simp [condVar, condExp_of_not_integrable, integrable_const_iff_isFiniteMeasure hc,
      integrable_const_iff_isFiniteMeasure <| pow_ne_zero _ hc, hμm, Pi.pow_def]
/-
**ProbabilityTheory.stronglyMeasurable_condVar** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：stronglyMeasurable_condVar : StronglyMeasurable[m] (Var[X; μ | m])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
-/
lemma stronglyMeasurable_condVar : StronglyMeasurable[m] (Var[X; μ | m]) :=
  stronglyMeasurable_condExp
/-
**ProbabilityTheory.condVar_congr_ae** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condVar_congr_ae (h : X =ᵐ[μ] Y) : Var[X; μ | m] =ᵐ[μ] Var[Y; μ | m]
参数：h : X =ᵐ[μ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma condVar_congr_ae (h : X =ᵐ[μ] Y) : Var[X; μ | m] =ᵐ[μ] Var[Y; μ | m] :=
  condExp_congr_ae <| by filter_upwards [h, condExp_congr_ae h] with ω hω hω'; dsimp; rw [hω, hω']
/-
**ProbabilityTheory.condVar_of_aestronglyMeasurable** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：condVar_of_aestronglyMeasurable [hμm : SigmaFinite (μ.trim hm)] (hX : AESt
ronglyMeasurable[m] X μ) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) : Var[X; μ 
| m] =ᵐ[μ] (X - μ[X | m]) ^ 2
参数：μ.trim hm；hX : AEStronglyMeasurable[m] X μ；hXint : Integrable ((X - μ[X | m])
 ^ 2) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_aestronglyMeasurable'`：condExp_of_aestronglyMea
surable' (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : AEStr
onglyMeasurable[m] f μ) (hfi : Integ…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
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
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
-/
lemma condVar_of_aestronglyMeasurable [hμm : SigmaFinite (μ.trim hm)]
    (hX : AEStronglyMeasurable[m] X μ) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) :
    Var[X; μ | m] =ᵐ[μ] (X - μ[X | m]) ^ 2 :=
  condExp_of_aestronglyMeasurable' _ ((continuous_pow _).comp_aestronglyMeasurable
    (hX.sub stronglyMeasurable_condExp.aestronglyMeasurable)) hXint
/-
**ProbabilityTheory.integrable_condVar** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：integrable_condVar : Integrable Var[X; μ | m] μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
-/
lemma integrable_condVar : Integrable Var[X; μ | m] μ := integrable_condExp

/-- The integral of the conditional variance `Var[X | m]` over an `m`-measurable set is equal to
the integral of `(X - μ[X | m]) ^ 2` on that set. -/
/-
**ProbabilityTheory.setIntegral_condVar** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：setIntegral_condVar [SigmaFinite (μ.trim hm)] (hX : Integrable ((X - μ[X |
 m]) ^ 2) μ) (hs : MeasurableSet[m] s) : ∫ ω in s, (Var[X; μ | m]) ω ∂μ = ∫ ω in
 s, (X ω - (μ[X | m]) ω) ^ 2 ∂μ
参数：μ.trim hm；hX : Integrable ((X - μ[X | m]) ^ 2) μ；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…

--- 原说明 ---
The integral of the conditional variance `Var[X | m]` over an `m`-measurable set
 is equal to
the integral of `(X - μ[X | m]) ^ 2` on that set.
-/
lemma setIntegral_condVar [SigmaFinite (μ.trim hm)] (hX : Integrable ((X - μ[X | m]) ^ 2) μ)
    (hs : MeasurableSet[m] s) :
    ∫ ω in s, (Var[X; μ | m]) ω ∂μ = ∫ ω in s, (X ω - (μ[X | m]) ω) ^ 2 ∂μ :=
  setIntegral_condExp _ hX hs

-- `(· ^ 2)` is a postfix operator called `_sq` in lemma names, but
-- `condVar_ae_eq_condExp_sq_sub_condExp_sq` is a bit ridiculous, so we exceptionally denote it by
-- `sq_` as it were a prefix.
/-
**ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：condVar_ae_eq_condExp_sq_sub_sq_condExp (hm : m <= m₀) [IsFiniteMeasure μ]
 (hX : MemLp X 2 μ) : Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2
参数：hm : m <= m₀；hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condVar.eq_1`：∀ {Ω : Type u_1} {m₀ : MeasurableSpace Ω
} (m : MeasurableSpace Ω) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   Probabili
tyTheory.condVar m X…
· 使用引理 `sub_sq`：sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
· 使用定理 `MeasureTheory.MemLp.integrable_sq`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.MemLp f 2 μ → Mea
sureTheory.Integrable (…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.mul`：∀ {α : Type u_1} {x : MeasurableSpace α} {𝕜 : T
ype u_2} [inst : NormedRing 𝕜] {μ : MeasureTheory.Measure α}   {p q r : ENNReal}
 {f φ : α → 𝕜…
· 使用定理 `MeasureTheory.MemLp.condExp`：∀ {α : Type u_1} {m m0 : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAddCommGroup E]   [i
nst_1 : NormedSpa…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.condExp_ofNat`：condExp_ofNat (n : Nat) [n.AtLeastTwo] (f :
 α -> R) : μ[ofNat(n) * f | m] =ᵐ[μ] ofNat(n) * μ[f | m]
· 使用引理 `MeasureTheory.condExp_mul_of_stronglyMeasurable_right`：condExp_mul_of_st
ronglyMeasurable_right {f g : Ω -> Real} (hg : StronglyMeasurable[m] g) (hfg : I
ntegrable (f * g) μ) (hf : Integrable f μ) …
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
（共 81 条，此处仅展示前 30 条）
-/
lemma condVar_ae_eq_condExp_sq_sub_sq_condExp (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 := by
  calc
    Var[X; μ | m]
    _ = μ[X ^ 2 - 2 * X * μ[X | m] + μ[X | m] ^ 2 | m] := by rw [condVar, sub_sq]
    _ =ᵐ[μ] μ[X ^ 2 | m] - 2 * μ[X | m] ^ 2 + μ[X | m] ^ 2 := by
      have aux₀ : Integrable (X ^ 2) μ := hX.integrable_sq
      have aux₁ : Integrable (2 * X * μ[X | m]) μ := by
        rw [mul_assoc]
        exact (memLp_one_iff_integrable.1 <| (hX.condExp one_le_two).mul hX).const_mul _
      have aux₂ : Integrable (μ[X | m] ^ 2) μ := (hX.condExp one_le_two).integrable_sq
      filter_upwards [condExp_add (m := m) (aux₀.sub aux₁) aux₂, condExp_sub (m := m) aux₀ aux₁,
        condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp aux₁
          ((hX.integrable one_le_two).const_mul _), condExp_ofNat (m := m) 2 X]
        with ω hω₀ hω₁ hω₂ hω₃
      simp [hω₀, hω₁, hω₂, hω₃,
        condExp_of_stronglyMeasurable hm (stronglyMeasurable_condExp.pow _) aux₂]
      simp [mul_assoc, sq]
    _ = μ[X ^ 2 | m] - μ[X | m] ^ 2 := by ring
/-
**ProbabilityTheory.condVar_ae_le_condExp_sq** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：condVar_ae_le_condExp_sq (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 
2 μ) : Var[X; μ | m] <=ᵐ[μ] μ[X ^ 2 | m]
参数：hm : m <= m₀；hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`：condVar_ae_eq
_condExp_sq_sub_sq_condExp (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
 : Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 57 条，此处仅展示前 30 条）
-/
lemma condVar_ae_le_condExp_sq (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m] := by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX] with ω hω
  dsimp at hω
  nlinarith

/-- **Law of total variance** -/
/-
**ProbabilityTheory.integral_condVar_add_variance_condExp** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：integral_condVar_add_variance_condExp (hm : m <= m₀) [IsProbabilityMeasure
 μ] (hX : MemLp X 2 μ) : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ]
参数：hm : m <= m₀；hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用引理 `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`：condVar_ae_eq
_condExp_sq_sub_sq_condExp (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
 : Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.variance_eq_sub`：variance_eq_sub [IsProbabilityMeasure
 μ] {X : Ω -> Real} (hX : MemLp X 2 μ) : variance X μ = μ[X ^ 2] - μ[X] ^ 2
· 使用定理 `MeasureTheory.MemLp.condExp`：∀ {α : Type u_1} {m m0 : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAddCommGroup E]   [i
nst_1 : NormedSpa…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.MemLp.integrable_sq`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.MemLp f 2 μ → Mea
sureTheory.Integrable (…
· 使用定理 `MeasureTheory.integral_condExp`：integral_condExp (hm : m <= m₀) [hμm : S
igmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
**Law of total variance**
-/
lemma integral_condVar_add_variance_condExp (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] := by
  calc
    μ[Var[X; μ | m]] + Var[μ[X | m]; μ]
    _ = μ[(μ[X ^ 2 | m] - μ[X | m] ^ 2 : Ω → ℝ)] + (μ[μ[X | m] ^ 2] - μ[μ[X | m]] ^ 2) := by
      congr 1
      · exact integral_congr_ae <| condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX
      · exact variance_eq_sub (hX.condExp one_le_two)
    _ = μ[X ^ 2] - μ[μ[X | m] ^ 2] + (μ[μ[X | m] ^ 2] - μ[X] ^ 2) := by
      rw [integral_sub' integrable_condExp, integral_condExp hm, integral_condExp hm]
      exact (hX.condExp one_le_two).integrable_sq
    _ = Var[X; μ] := by rw [variance_eq_sub hX]; ring
/-
**ProbabilityTheory.condVar_bot'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condVar_bot' [NeZero μ] (X : Ω -> Real) : Var[X; μ | ⊥] = fun _ => ⨍ ω, (X
 ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ
参数：X : Ω -> Real。
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
· 使用定理 `MeasureTheory.condExp_bot'`：condExp_bot' [hμ : NeZero μ] (f : α -> E) : 
μ[f | ⊥] = fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condVar_bot' [NeZero μ] (X : Ω → ℝ) :
    Var[X; μ | ⊥] = fun _ => ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ := by
  simp [condVar, condExp_bot', average, measureReal_def]
/-
**ProbabilityTheory.condVar_bot_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：condVar_bot_ae_eq (X : Ω -> Real) : Var[X; μ | ⊥] =ᵐ[μ] fun _ => ⨍ ω, (X ω
 - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ
参数：X : Ω -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.condVar_bot'`：condVar_bot' [NeZero μ] (X : Ω -> Real) 
: Var[X; μ | ⊥] = fun _ => ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ
-/
lemma condVar_bot_ae_eq (X : Ω → ℝ) :
    Var[X; μ | ⊥] =ᵐ[μ] fun _ ↦ ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ := by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · rw [ae_zero]
    exact eventually_bot
  · exact .of_forall <| congr_fun (condVar_bot' X)

@[simp]
/-
**ProbabilityTheory.condVar_bot** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condVar_bot [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) : Var[X; μ | 
⊥] = fun _ω => Var[X; μ]
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condVar_bot'`：condVar_bot' [NeZero μ] (X : Ω -> Real) 
: Var[X; μ | ⊥] = fun _ => ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condVar_bot [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) :
    Var[X; μ | ⊥] = fun _ω ↦ Var[X; μ] := by
  simp [condVar_bot', average_eq_integral, variance_eq_integral hX]
/-
**ProbabilityTheory.condVar_smul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condVar_smul (c : Real) (X : Ω -> Real) : Var[c • X; μ | m] =ᵐ[μ] c ^ 2 • 
Var[X; μ | m]
参数：c : Real；X : Ω -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condVar.eq_1`：∀ {Ω : Type u_1} {m₀ : MeasurableSpace Ω
} (m : MeasurableSpace Ω) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   Probabili
tyTheory.condVar m X…
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_smul`：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : 
α -> E) (m : MeasurableSpace α) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condVar_smul (c : ℝ) (X : Ω → ℝ) : Var[c • X; μ | m] =ᵐ[μ] c ^ 2 • Var[X; μ | m] := by
  calc
    Var[c • X; μ | m]
    _ =ᵐ[μ] μ[c ^ 2 • (X - μ[X | m]) ^ 2 | m] := by
      rw [condVar]
      refine condExp_congr_ae ?_
      filter_upwards [condExp_smul (m := m) c X] with ω hω
      simp [hω, ← mul_sub, mul_pow]
    _ =ᵐ[μ] c ^ 2 • Var[X; μ | m] := condExp_smul ..
/-
**ProbabilityTheory.condVar_neg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {m₀ m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
(X : Ω → ℝ),   ProbabilityTheory.condVar m (-X) μ =ᵐ[μ] ProbabilityTheory.condVa
r m X μ
参数：X : Ω → ℝ；-X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
（共 53 条，此处仅展示前 30 条）
-/
@[simp] lemma condVar_neg (X : Ω → ℝ) : Var[-X; μ | m] =ᵐ[μ] Var[X; μ | m] := by
  refine condExp_congr_ae ?_
  filter_upwards [condExp_neg (m := m) X] with ω hω
  simp [hω]
  ring

end ProbabilityTheory

