/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Basic properties of the risk of an estimator

## Main statements

* `iSup_bayesRisk_le_minimaxRisk`: the maximal Bayes risk is less than or equal to the minimax risk.
* `bayesRisk_le_bayesRisk_comp`: data-processing inequality for the Bayes risk with respect to a
  prior: if we compose the data generating kernel `P` with a Markov kernel, then the Bayes risk
  increases.
* `bayesRisk_le_iInf`: for `P` a Markov kernel, the Bayes risk is less than `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

In several cases, there is no information in the data about the parameter and the Bayes risk takes
its maximal value.
* `bayesRisk_const`: if the data generating kernel is constant, then the Bayes risk is equal to
  `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.
* `bayesRisk_of_subsingleton`: if the observation space is a subsingleton, then the Bayes risk is
  equal to `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

## TODO

In many cases, the maximal Bayes risk and the minimax risk are equal
(by a so-called minimax theorem).

-/

public section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section BayesRiskLeMinimaxRisk

/-
**ProbabilityTheory.avgRisk_le_iSup_risk** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：avgRisk_le_iSup_risk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel
 𝓧 𝓨) (π : Measure Θ) [IsProbabilityMeasure π] : avgRisk ℓ P κ π <= ⨆ θ, ∫⁻ y, ℓ
 θ y ∂((κ ∘ₖ P) θ)
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.lintegral_le_iSup`：lintegral_le_iSup [IsProbabilityMeasure
 μ] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ <= ⨆ x, f x
-/
lemma avgRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    avgRisk ℓ P κ π ≤ ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := lintegral_le_iSup _
/-
**ProbabilityTheory.bayesRisk_le_avgRisk** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：bayesRisk_le_avgRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel
 𝓧 𝓨) (π : Measure Θ) [hκ : IsMarkovKernel κ] : bayesRisk ℓ P π <= avgRisk ℓ P κ
 π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma bayesRisk_le_avgRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRisk ℓ P π ≤ avgRisk ℓ P κ π := iInf₂_le κ hκ
/-
**ProbabilityTheory.bayesRisk_le_minimaxRisk** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：bayesRisk_le_minimaxRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π : Me
asure Θ) [IsProbabilityMeasure π] : bayesRisk ℓ P π <= minimaxRisk ℓ P
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用引理 `ProbabilityTheory.avgRisk_le_iSup_risk`：avgRisk_le_iSup_risk (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) [IsProbabilityMe
asure π] : avgRisk ℓ P κ π <…
-/
lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRisk ℓ P π ≤ minimaxRisk ℓ P := iInf₂_mono fun _ _ ↦ avgRisk_le_iSup_risk _ _ _ _

/-- The maximal Bayes risk is less than or equal to the minimax risk. -/
/-
**ProbabilityTheory.iSup_bayesRisk_le_minimaxRisk** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：iSup_bayesRisk_le_minimaxRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) : 
⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π <= minimaxRisk ℓ
 P
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用引理 `ProbabilityTheory.bayesRisk_le_minimaxRisk`：bayesRisk_le_minimaxRisk (ℓ 
: Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) [IsProbabilityMeasure π] 
: bayesRisk ℓ P π <= minimaxRisk…

--- 原说明 ---
The maximal Bayes risk is less than or equal to the minimax risk.
-/
lemma iSup_bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π
      ≤ minimaxRisk ℓ P := iSup₂_le fun _ _ ↦ bayesRisk_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Const

/-- See `avgRisk_const_left'` for a similar result with integrals swapped. -/
/-
**ProbabilityTheory.avgRisk_const_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：avgRisk_const_left (ℓ : Θ -> 𝓨 -> Real>=0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 
𝓨) (π : Measure Θ) : avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ
 μ) ∂π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；μ : Measure 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `avgRisk_const_left'` for a similar result with integrals swapped.
-/
lemma avgRisk_const_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ μ) ∂π := by
  simp [avgRisk]

/-- See `avgRisk_const_left` for a similar result with integrals swapped. -/
/-
**ProbabilityTheory.avgRisk_const_left'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：avgRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite
 μ] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] : avgRisk ℓ
 (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ)
参数：hl : Measurable (uncurry ℓ)；μ : Measure 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_const_left`：avgRisk_const_left (ℓ : Θ -> 𝓨 -> 
Real>=0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : avgRisk ℓ (Kernel.c
onst Θ μ) κ π = ∫⁻ θ, ∫⁻ y…
· 使用定理 `MeasureTheory.lintegral_lintegral_swap`：lintegral_lintegral_swap [SFinit
e μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x,
 ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫…
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
See `avgRisk_const_left` for a similar result with integrals swapped.
-/
lemma avgRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := by
  rw [avgRisk_const_left, lintegral_lintegral_swap (by fun_prop)]

/-- See `avgRisk_const_right` for a simpler result when `P` is a Markov kernel. -/
/-
**ProbabilityTheory.avgRisk_const_right'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：avgRisk_const_right' (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measur
e 𝓨) (π : Measure Θ) : avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y
, ℓ θ y ∂ν ∂π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；ν : Measure 𝓨；π : Measure Θ。
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.Kernel.const_comp`：const_comp (μ : Measure γ) (κ : Ker
nel α β) : const β μ ∘ₖ κ = fun a => (κ a) Set.univ • μ
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `avgRisk_const_right` for a simpler result when `P` is a Markov kernel.
-/
lemma avgRisk_const_right' (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk, Kernel.const_comp]

/-- See `avgRisk_const_right'` for a similar result when `P` is not a Markov kernel. -/
/-
**ProbabilityTheory.avgRisk_const_right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：avgRisk_const_right (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) [IsMarkovKer
nel P] (ν : Measure 𝓨) (π : Measure Θ) : avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ
, ∫⁻ y, ℓ θ y ∂ν ∂π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；ν : Measure 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_const_right'`：avgRisk_const_right' (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) : avgRisk ℓ P (Ke
rnel.const 𝓧 ν) π = ∫⁻ θ, P …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `avgRisk_const_right'` for a similar result when `P` is not a Markov kernel.
-/
lemma avgRisk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk_const_right']

/-- See `bayesRisk_le_iInf` for a simpler result when `P` is a Markov kernel. -/
/-
**ProbabilityTheory.bayesRisk_le_iInf'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：bayesRisk_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Mea
sure Θ) : bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π
参数：hl : Measurable (uncurry ℓ)；P : Kernel Θ 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_const_right'`：avgRisk_const_right' (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) : avgRisk ℓ P (Ke
rnel.const 𝓧 ν) π = ∫⁻ θ, P …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a

--- 原说明 ---
See `bayesRisk_le_iInf` for a simpler result when `P` is a Markov kernel.
-/
lemma bayesRisk_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right', mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

/-- See `bayesRisk_le_iInf'` for a similar result when `P` is not a Markov kernel. -/
/-
**ProbabilityTheory.bayesRisk_le_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：bayesRisk_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkov
Kernel P] (π : Measure Θ) : bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, ℓ θ y ∂π
参数：hl : Measurable (uncurry ℓ)；P : Kernel Θ 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ProbabilityTheory.bayesRisk_le_iInf'`：bayesRisk_le_iInf' (hl : Measurabl
e (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) : bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, 
ℓ θ y * P θ .univ ∂π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `bayesRisk_le_iInf'` for a similar result when `P` is not a Markov kernel.
-/
lemma bayesRisk_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y, ∫⁻ θ, ℓ θ y ∂π :=
  (bayesRisk_le_iInf' hl P π).trans_eq (by simp)
/-
**ProbabilityTheory.bayesRisk_const'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：bayesRisk_const' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
 (π : Measure Θ) [SFinite π] (hl_pos : μ .univ = ∞ -> ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 ->
 exists y, ∫⁻ θ, ℓ θ y ∂π = 0) (h_zero : μ = 0 -> Nonempty 𝓨) : bayesRisk ℓ (Ker
nel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π
参数：hl : Measurable (uncurry ℓ)；μ : Measure 𝓧；π : Measure Θ；hl_pos : μ .univ = ∞ 
-> ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 -> exists y, ∫⁻ θ, ℓ θ y ∂π = 0；h_zero : μ = 0 -> Non
empty 𝓨。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ProbabilityTheory.bayesRisk_le_iInf'`：bayesRisk_le_iInf' (hl : Measurabl
e (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) : bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, 
ℓ θ y * P θ .univ ∂π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_const_left'`：avgRisk_const_left' (hl : Measura
ble (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ
] (π : Measure Θ) [SFinite …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `MeasureTheory.Measure.comp_apply_univ`：comp_apply_univ [IsMarkovKernel κ
] : (κ ∘ₘ μ) Set.univ = μ Set.univ
· 使用引理 `ENNReal.iInf_mul'`：iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `MeasureTheory.lintegral_mul_const`：lintegral_mul_const (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.iInf_mul_le_lintegral`：iInf_mul_le_lintegral (f : α -> Rea
l>=0∞) : (⨅ x, f x) * μ .univ <= ∫⁻ x, f x ∂μ
-/
lemma bayesRisk_const' (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ → ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 → ∃ y, ∫⁻ θ, ℓ θ y ∂π = 0)
    (h_zero : μ = 0 → Nonempty 𝓨) :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y ↦ ∫⁻ θ, ℓ θ y ∂π))
  rw [Measure.comp_apply_univ, ENNReal.iInf_mul' hl_pos (fun hμ ↦ h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop
/-
**ProbabilityTheory.bayesRisk_const_of_neZero** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：bayesRisk_const_of_neZero (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [N
eZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] : bayesRisk ℓ (Kernel.c
onst Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π
参数：hl : Measurable (uncurry ℓ)；μ : Measure 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.bayesRisk_const'`：bayesRisk_const' (hl : Measurable (u
ncurry ℓ)) (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π] (hl_pos : μ .
univ = ∞ -> ⨅ y, ∫⁻ θ, ℓ…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma bayesRisk_const_of_neZero (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])
/-
**ProbabilityTheory.bayesRisk_const_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：bayesRisk_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ)) (μ 
: Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] : bayesRisk ℓ (Kern
el.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π
参数：hl : Measurable (uncurry ℓ)；μ : Measure 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.bayesRisk_const'`：bayesRisk_const' (hl : Measurable (u
ncurry ℓ)) (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π] (hl_pos : μ .
univ = ∞ -> ⨅ y, ∫⁻ θ, ℓ…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma bayesRisk_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (fun _ ↦ inferInstance)
/-
**ProbabilityTheory.bayesRisk_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：bayesRisk_const (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [IsProbabili
tyMeasure μ] (π : Measure Θ) [SFinite π] : bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ 
y, ∫⁻ θ, ℓ θ y ∂π
参数：hl : Measurable (uncurry ℓ)；μ : Measure 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bayesRisk_const_of_neZero`：bayesRisk_const_of_neZero (
hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π :
 Measure Θ) [SFinite π] : bayesRi…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_const (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_const_of_neZero hl μ π]

end Const

section Bounds

/-- See `avgRisk_le_mul` for the usual case in which `π` is a probability measure and the kernels
are Markov. -/
/-
**ProbabilityTheory.avgRisk_le_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) {C : Rea
l>=0} (hℓC : forall θ y, ℓ θ y <= C) : avgRisk ℓ P κ π <= C * κ.bound * P.bound 
* π Set.univ
参数：P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ；hℓC : forall θ y, ℓ θ y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound

--- 原说明 ---
See `avgRisk_le_mul` for the usual case in which `π` is a probability measure an
d the kernels
are Markov.
-/
lemma avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
    {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C * κ.bound * P.bound * π Set.univ :=
  calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ ≤ ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by gcongr with θ y; exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ ≤ ∫⁻ θ, C * ∫⁻ x, κ.bound ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ ≤ ∫⁻ θ, C * κ.bound * P.bound ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * κ.bound * P.bound * π Set.univ := by simp
/-
**ProbabilityTheory.avgRisk_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：avgRisk_le_mul (P : Kernel Θ 𝓧) [IsMarkovKernel P] (κ : Kernel 𝓧 𝓨) [IsMar
kovKernel κ] (π : Measure Θ) [IsProbabilityMeasure π] {C : Real>=0} (hℓC : foral
l θ y, ℓ θ y <= C) : avgRisk ℓ P κ π <= C
参数：P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ；hℓC : forall θ y, ℓ θ y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ProbabilityTheory.avgRisk_le_mul'`：avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ :
 Kernel 𝓧 𝓨) (π : Measure Θ) {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) : avgR
isk ℓ P κ π <= C * κ.bo…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty`：bound_eq_zero_of_isEm
pty [IsEmpty α] (κ : Kernel α β) : κ.bound = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty'`：bound_eq_zero_of_isE
mpty' [IsEmpty β] (κ : Kernel α β) : κ.bound = 0
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_one`：bound_eq_one [Nonempty α] (κ : Ke
rnel α β) [IsMarkovKernel κ] : κ.bound = 1
-/
lemma avgRisk_le_mul (P : Kernel Θ 𝓧) [IsMarkovKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C := by
  refine (avgRisk_le_mul' P κ π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ
  · simp
  · rcases isEmpty_or_nonempty 𝓧 <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is bounded by a constant.
See `bayesRisk_le_mul` for the usual cases where all measures are probability measures. -/
/-
**ProbabilityTheory.bayesRisk_le_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧) (π : Measure Θ) {C : 
Real>=0} (hℓC : forall θ y, ℓ θ y <= C) : bayesRisk ℓ P π <= C * P.bound * π Set
.univ
参数：P : Kernel Θ 𝓧；π : Measure Θ；hℓC : forall θ y, ℓ θ y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ProbabilityTheory.bayesRisk_le_avgRisk`：bayesRisk_le_avgRisk (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) [hκ : IsMarkovKe
rnel κ] : bayesRisk ℓ P π <=…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `ProbabilityTheory.avgRisk_le_mul'`：avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ :
 Kernel 𝓧 𝓨) (π : Measure Θ) {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) : avgR
isk ℓ P κ π <= C * κ.bo…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty`：bound_eq_zero_of_isEm
pty [IsEmpty α] (κ : Kernel α β) : κ.bound = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty'`：bound_eq_zero_of_isE
mpty' [IsEmpty β] (κ : Kernel α β) : κ.bound = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_one`：bound_eq_one [Nonempty α] (κ : Ke
rnel α β) [IsMarkovKernel κ] : κ.bound = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
For a bounded loss, the Bayes risk with respect to a prior is bounded by a const
ant.
See `bayesRisk_le_mul` for the usual cases where all measures are probability me
asures.
-/
lemma bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧) (π : Measure Θ)
    {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π ≤ C * P.bound * π Set.univ := by
  refine (bayesRisk_le_avgRisk ℓ P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π).trans ?_
  refine (avgRisk_le_mul' P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC).trans ?_
  rcases isEmpty_or_nonempty 𝓧 <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is bounded by a constant. -/
/-
**ProbabilityTheory.bayesRisk_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：bayesRisk_le_mul [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsMarkovKernel P] (π : Mea
sure Θ) [IsProbabilityMeasure π] {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) : 
bayesRisk ℓ P π <= C
参数：P : Kernel Θ 𝓧；π : Measure Θ；hℓC : forall θ y, ℓ θ y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ProbabilityTheory.bayesRisk_le_mul'`：bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨]
 (P : Kernel Θ 𝓧) (π : Measure Θ) {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
 bayesRisk ℓ P π <= C * P…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_zero_of_isEmpty`：bound_eq_zero_of_isEm
pty [IsEmpty α] (κ : Kernel α β) : κ.bound = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `ProbabilityTheory.Kernel.bound_eq_one`：bound_eq_one [Nonempty α] (κ : Ke
rnel α β) [IsMarkovKernel κ] : κ.bound = 1

--- 原说明 ---
For a bounded loss, the Bayes risk with respect to a prior is bounded by a const
ant.
-/
lemma bayesRisk_le_mul [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π ≤ C := by
  refine (bayesRisk_le_mul' P π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is finite. -/
/-
**ProbabilityTheory.bayesRisk_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：bayesRisk_lt_top [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Mea
sure Θ) [IsFiniteMeasure π] {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) : bayes
Risk ℓ P π < ∞
参数：P : Kernel Θ 𝓧；π : Measure Θ；hℓC : forall θ y, ℓ θ y <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ProbabilityTheory.bayesRisk_le_mul'`：bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨]
 (P : Kernel Θ 𝓧) (π : Measure Θ) {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
 bayesRisk ℓ P π <= C * P…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal

--- 原说明 ---
For a bounded loss, the Bayes risk with respect to a prior is finite.
-/
lemma bayesRisk_lt_top [Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π < ∞ := by
  refine (bayesRisk_le_mul' P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, P.bound_lt_top]

end Bounds

/-
**ProbabilityTheory.bayesRisk_discard** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：bayesRisk_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π
] : bayesRisk ℓ (Kernel.discard Θ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π
参数：hl : Measurable (uncurry ℓ)；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.discard_eq_const`：discard_eq_const : discard α 
= const α (Measure.dirac PUnit.unit)
· 使用引理 `ProbabilityTheory.bayesRisk_const`：bayesRisk_const (hl : Measurable (unc
urry ℓ)) (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] : 
bayesRisk ℓ (Kernel.con…
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
-/
lemma bayesRisk_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.discard Θ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  rw [Kernel.discard_eq_const, bayesRisk_const hl]

section Subsingleton

variable [Subsingleton 𝓧] [Nonempty 𝓨]

/-
**ProbabilityTheory.bayesRisk_eq_iInf_measure_of_subsingleton** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：bayesRisk_eq_iInf_measure_of_subsingleton : bayesRisk ℓ P π = ⨅ (μ : Measu
re 𝓨) (_ : IsProbabilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ) π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bayesRisk_of_isEmpty`：bayesRisk_of_isEmpty [IsEmpty 𝓧]
 : bayesRisk ℓ P π = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_of_isEmpty`：avgRisk_of_isEmpty [IsEmpty 𝓧] : a
vgRisk ℓ P κ π = 0
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `MeasureTheory.instNonemptySubtypeMeasureIsProbabilityMeasure`：∀ {α : Typ
e u_1} [inst : MeasurableSpace α] [hα : Nonempty α], Nonempty { μ // MeasureTheo
ry.IsProbabilityMeasure μ }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.bayesRisk.eq_1`：∀ {Θ : Type u_1} {𝓧 : Type u_2} {𝓨 : T
ype u_3} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}   [inst : MeasurableS
pace 𝓨] (ℓ : Θ → 𝓨 → E…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [self : ProbabilityTh…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 InfSet α] {g : ι' → α} (e : ι ≃ ι'), ⨅ x, g (e x) = ⨅ y, g y
-/
lemma bayesRisk_eq_iInf_measure_of_subsingleton :
    bayesRisk ℓ P π
      = ⨅ (μ : Measure 𝓨) (_ : IsProbabilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ) π := by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := hX.some
  rw [bayesRisk, iInf_subtype', iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, κ.2.isProbabilityMeasure x⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, ⟨fun _ ↦ μ.2⟩⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  rfl
/-
**ProbabilityTheory.bayesRisk_of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：bayesRisk_of_subsingleton' [SFinite π] (hl : Measurable (uncurry ℓ)) : bay
esRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π
参数：hl : Measurable (uncurry ℓ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ProbabilityTheory.bayesRisk_le_iInf'`：bayesRisk_le_iInf' (hl : Measurabl
e (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) : bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, 
ℓ θ y * P θ .univ ∂π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bayesRisk_eq_iInf_measure_of_subsingleton`：bayesRisk_e
q_iInf_measure_of_subsingleton : bayesRisk ℓ P π = ⨅ (μ : Measure 𝓨) (_ : IsProb
abilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_const_right'`：avgRisk_const_right' (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) : avgRisk ℓ P (Ke
rnel.const 𝓧 ν) π = ∫⁻ θ, P …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `MeasureTheory.iInf_le_lintegral`：iInf_le_lintegral [IsProbabilityMeasure
 μ] (f : α -> Real>=0∞) : ⨅ x, f x <= ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.lintegral_lintegral_swap`：lintegral_lintegral_swap [SFinit
e μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x,
 ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `MeasureTheory.lintegral_mul_const`：lintegral_mul_const (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
（共 31 条，此处仅展示前 30 条）
-/
lemma bayesRisk_of_subsingleton' [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right', le_iInf_iff]
  refine fun μ hμ ↦ (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  · have := P.measurable_coe .univ
    fun_prop
/-
**ProbabilityTheory.bayesRisk_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：bayesRisk_of_subsingleton [IsMarkovKernel P] [SFinite π] (hl : Measurable 
(uncurry ℓ)) : bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π
参数：hl : Measurable (uncurry ℓ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bayesRisk_of_subsingleton'`：bayesRisk_of_subsingleton'
 [SFinite π] (hl : Measurable (uncurry ℓ)) : bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y 
* P θ .univ ∂π
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_of_subsingleton [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_of_subsingleton' hl]

end Subsingleton

section Compositions

/-- **Data processing inequality** for the Bayes risk with respect to a prior: composition of the
data generating kernel by a Markov kernel increases the risk. -/
/-
**ProbabilityTheory.bayesRisk_le_bayesRisk_comp** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：bayesRisk_le_bayesRisk_comp (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π :
 Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] : bayesRisk ℓ P π <= bayesRisk 
ℓ (η ∘ₖ P) π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；π : Measure Θ；η : Kernel 𝓧 𝓧'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
**Data processing inequality** for the Bayes risk with respect to a prior: compo
sition of the
data generating kernel by a Markov kernel increases the risk.
-/
lemma bayesRisk_le_bayesRisk_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ P π ≤ bayesRisk ℓ (η ∘ₖ P) π := by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

/-- **Data processing inequality** for the Bayes risk with respect to a prior: taking the map of
the data generating kernel by a function increases the risk. -/
/-
**ProbabilityTheory.bayesRisk_le_bayesRisk_map** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：bayesRisk_le_bayesRisk_map (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π : 
Measure Θ) {f : 𝓧 -> 𝓧'} (hf : Measurable f) : bayesRisk ℓ P π <= bayesRisk ℓ (P
.map f) π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；π : Measure Θ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用引理 `ProbabilityTheory.bayesRisk_le_bayesRisk_comp`：bayesRisk_le_bayesRisk_co
mp (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) (η : Kernel 𝓧 𝓧') [
IsMarkovKernel η] : bayesRisk ℓ P π…

--- 原说明 ---
**Data processing inequality** for the Bayes risk with respect to a prior: takin
g the map of
the data generating kernel by a function increases the risk.
-/
lemma bayesRisk_le_bayesRisk_map (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) {f : 𝓧 → 𝓧'} (hf : Measurable f) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ (P.map f) π := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _
/-
**ProbabilityTheory.bayesRisk_compProd_le_bayesRisk** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：bayesRisk_compProd_le_bayesRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) 
[IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
 bayesRisk ℓ (P otimesₖ η) π <= bayesRisk ℓ P π
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；π : Measure Θ；η : Kernel (Θ × 𝓧) 𝓧'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd`：fst_compProd (κ : Kernel α β) (η 
: Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] : fst (κ otimesₖ η) =
 κ
· 使用引理 `ProbabilityTheory.bayesRisk_le_bayesRisk_comp`：bayesRisk_le_bayesRisk_co
mp (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) (η : Kernel 𝓧 𝓧') [
IsMarkovKernel η] : bayesRisk ℓ P π…
-/
lemma bayesRisk_compProd_le_bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ (P ⊗ₖ η) π ≤ bayesRisk ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ η) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

end Compositions

end ProbabilityTheory

