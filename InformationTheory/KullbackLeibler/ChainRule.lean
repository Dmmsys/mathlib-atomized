/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Notation

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Chain rule for the Kullback-Leibler divergence

Suppose that we have two finite joint measures on a product `𝓧 × 𝓨`, which can be decomposed as
`μ ⊗ₘ κ` and `ν ⊗ₘ η`, where `μ` and `ν` are measures on `𝓧` and `κ` and `η` are Markov kernels
from `𝓧` to `𝓨`. Then we can express the Kullback-Leibler divergence between these two joint
measures as a sum of `klDiv μ ν` and the conditional Kullback-Leibler divergence between the kernels
`κ` and `η`, averaged over `μ`. The resulting equality is most often written as
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + μ[fun x ↦ klDiv (κ x) (η x)]`.

Here we first prove the following version:
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.
This version avoids the issue of measurability of the function `x ↦ klDiv (κ x) (η x)`, which is not
always guaranteed, and thus holds for all measurable spaces `𝓧` and `𝓨`, without any assumptions.

## Main statements

* `klDiv_compProd_eq_add`: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`
* `klDiv_compProd_left`: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν`

## Proof

The main ingredient is the chain rule for Radon-Nikodym derivatives:
`∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) = ∂μ/∂ν * ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
Then, omitting edge cases, the Kullback-Leibler divergence is an integral of a logarithm of the
derivative on the left, which decomposes into a sum of two integrals of logarithms.
We now give a more detailed outline of the proof.

The Kullback-Leibler divergence `klDiv μ ν` is defined with an if-then-else statement:
if the measures are absolutely continuous (`μ ≪ ν`) and the log-likelihood ratio `llr μ ν` is
integrable, then it is defined as `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, otherwise
it is defined to be `∞`.

We first deal with the case in which absolute continuity does not hold. The main observation is
that `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η`, which means that if one of the two sides of the
KL equality is infinite because of lack of absolute continuity, then the other side is also infinite
for the same reason.

Then, we deal with the case in which absolute continuity holds but integrability does not. Again,
we can show a similar equivalence for integrability, which allows us to conclude that both sides
are infinite.
`Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)` is equivalent to
`Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)`.
The proof of this equivalence relies on the convexity of the function `x ↦ x * log x`.

Finally, we prove the equality in the case in which both absolute continuity and integrability hold.
In that case, `klDiv μ ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` and similarly for
the other terms. It is easy to see that it suffices to prove the equality of the integrals parts.
Finally, the computation for the integral of the log-likelihood ratio is as follows:
```
∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
    (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η)
_ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ)
_ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) + ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ)
_ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ)
```

## TODO

Add a version of the chain rule for the integral form of the contional KL divergence, i.e.
`μ[fun x ↦ klDiv (κ x) (η x)]`.

-/

public section

open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]

/-- If the log-likelihood ration between two composition-products is integrable, then so is the
log-likelihood ratio between the two measures on the first space. -/
/-
**InformationTheory.integrable_llr_of_integrable_llr_compProd** 是 Mathlib 中的一个引理
，位于命名空间 `InformationTheory`。
形式化陈述：integrable_llr_of_integrable_llr_compProd (h_ac : μ otimesₘ κ ≪ ν otimesₘ 
η) (h_int : Integrable (llr (μ otimesₘ κ) (ν otimesₘ η)) (μ otimesₘ κ)) : Integr
able (llr μ ν) μ
参数：h_ac : μ otimesₘ κ ≪ ν otimesₘ η；h_int : Integrable (llr (μ otimesₘ κ) (ν oti
mesₘ η)) (μ otimesₘ κ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_iff`：absolutelyConti
nuous_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFinit
eKernel η] [forall x, NeZero (κ x)] : μ otime…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd`：∀ {𝓧 : Type u_
1} {m𝓧 : MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} {𝓨 : Type u_2} {m𝓨 :
 MeasurableSpace 𝓨}   {κ η : ProbabilityTheory…
· 使用定理 `Continuous.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α]   [inst
_3 : TopologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
· 使用引理 `Real.convexOn_mul_log`：convexOn_mul_log : ConvexOn Real (Set.Ici (0 : Re
al)) (fun x => x * log x)
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.integrable_rnDeriv_mul_log_iff`：integrable_rnDeriv_mul_log
_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) : Integrable 
(fun a => (μ.rnDeriv ν a).toReal *…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.instSFiniteProdCompProd`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ

--- 原说明 ---
If the log-likelihood ration between two composition-products is integrable, the
n so is the
log-likelihood ratio between the two measures on the first space.
-/
lemma integrable_llr_of_integrable_llr_compProd
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  replace h_int := convexOn_mul_log.integrable_apply_rnDeriv_of_integrable_compProd
    continuous_mul_log.stronglyMeasurable continuous_mul_log.continuousWithinAt h_int hκη_ac
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int
/-
**InformationTheory.rnDeriv_compProd_mul_log_eq_mul_add** 是 Mathlib 中的一个引理，位于命名空
间 `InformationTheory`。
形式化陈述：rnDeriv_compProd_mul_log_eq_mul_add (h_ac : μ otimesₘ κ ≪ μ otimesₘ η) : f
orallᵐ p ∂(ν otimesₘ η), ((∂μ otimesₘ κ/∂ν otimesₘ η) p).toReal * log ((∂μ otime
sₘ κ/∂ν otimesₘ η) p).toReal = (((∂μ otimesₘ κ/∂ν otimesₘ η) p).toReal * (log ((
∂μ/∂ν) p.1).toReal + log ((∂(μ otimesₘ κ)/∂(μ otimesₘ η)) p).toReal))
参数：h_ac : μ otimesₘ κ ≪ μ otimesₘ η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.rnDeriv_compProd`：rnDeriv_compProd [IsFiniteMeasure μ]
 [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : μ otimesₘ κ ≪ μ otimesₘ η) (ν : M
easure α) [IsFiniteMeasu…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
-/
lemma rnDeriv_compProd_mul_log_eq_mul_add (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ p ∂(ν ⊗ₘ η), ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal =
      (((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * (log ((∂μ/∂ν) p.1).toReal +
        log ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) p).toReal)) := by
  filter_upwards [rnDeriv_compProd h_ac ν] with p hp
  simp_rw [hp, ENNReal.toReal_mul]
  by_cases h_zero1 : ((∂μ/∂ν) p.1).toReal = 0
  · simp [h_zero1]
  by_cases h_zero2 : ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal = 0
  · simp [h_zero2]
  simp [log_mul h_zero1 h_zero2]
/-
**InformationTheory.integrable_llr_compProd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Infor
mationTheory`。
形式化陈述：integrable_llr_compProd_iff (h_ac : μ otimesₘ κ ≪ ν otimesₘ η) : Integrabl
e (llr (μ otimesₘ κ) (ν otimesₘ η)) (μ otimesₘ κ) ↔ Integrable (llr μ ν) μ ∧ Int
egrable (llr (μ otimesₘ κ) (μ otimesₘ η)) (μ otimesₘ κ)
参数：h_ac : μ otimesₘ κ ≪ ν otimesₘ η。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_iff`：absolutelyConti
nuous_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFinit
eKernel η] [forall x, NeZero (κ x)] : μ otime…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.integrable_rnDeriv_mul_log_iff`：integrable_rnDeriv_mul_log
_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) : Integrable 
(fun a => (μ.rnDeriv ν a).toReal *…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.instSFiniteProdCompProd`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `InformationTheory.rnDeriv_compProd_mul_log_eq_mul_add`：rnDeriv_compProd_
mul_log_eq_mul_add (h_ac : μ otimesₘ κ ≪ μ otimesₘ η) : forallᵐ p ∂(ν otimesₘ η)
, ((∂μ otimesₘ κ/∂ν otimesₘ η) p).toReal * …
· 使用引理 `MeasureTheory.integrable_toReal_rnDeriv_mul_iff`：integrable_toReal_rnDer
iv_mul_iff (hμν : μ ≪ ν) {f : α -> Real} : Integrable (fun x => (μ.rnDeriv ν x).
toReal * f x) ν ↔ Integrable f μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.integrable_compProd_iff`：integrable_compProd_iff [
SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] {f : α × β -> 
E} (hf : AEStronglyMeasurable f (μ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `MeasureTheory.stronglyMeasurable_llr`：stronglyMeasurable_llr (μ ν : Meas
ure α) : StronglyMeasurable (llr μ ν)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
（共 46 条，此处仅展示前 30 条）
-/
lemma integrable_llr_compProd_iff (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac,
    integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη),
    integrable_toReal_rnDeriv_mul_iff h_ac]
  have h_iff_κ : Integrable (llr μ ν) μ ↔ Integrable (fun x ↦ llr μ ν x.1) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    swap; · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
    simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
      Filter.eventually_true, integral_const, probReal_univ, smul_eq_mul, one_mul, true_and]
    rw [← integrable_norm_iff (by fun_prop)]
  rw [h_iff_κ]
  -- Goal of the form `Integrable (f + g) ↔ Integrable f ∧ Integrable g`
  refine ⟨fun h_int ↦ ?_, fun ⟨h_int1, h_int2⟩ ↦ h_int1.add h_int2⟩
  -- We now prove `Integrable (f + g) → Integrable f ∧ Integrable g`.
  -- We have one of those implications from the lemma `integrable_llr_of_integrable_llr_compProd`,
  -- say `Integrable (f + g) → Integrable f`.
  -- But given `Integrable f`, we have `Integrable (f + g) ↔ Integrable g` and thus we can also
  -- conclude `Integrable g`.
  have h_int_iff : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (fun x ↦ log ((∂μ/∂ν) x.1).toReal +
        log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ κ) := by
    have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
    rw [← integrable_rnDeriv_mul_log_iff h_ac,
      integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)]
    exact integrable_toReal_rnDeriv_mul_iff h_ac
  have h_int1 := integrable_llr_of_integrable_llr_compProd h_ac (h_int_iff.2 h_int)
  rw [h_iff_κ] at h_int1
  rw [integrable_add_iff_integrable_right'] at h_int
  · exact ⟨h_int1, h_int⟩
  · exact h_int1

/-- Chain rule for the integral of the log-likelihood ratio, under absolute continuity and
integrability assumptions. -/
/-
**InformationTheory.integral_llr_compProd_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `Info
rmationTheory`。
形式化陈述：integral_llr_compProd_eq_add (h_ac : μ otimesₘ κ ≪ ν otimesₘ η) (h_int : I
ntegrable (llr (μ otimesₘ κ) (ν otimesₘ η)) (μ otimesₘ κ)) : ∫ p, llr (μ otimesₘ
 κ) (ν otimesₘ η) p ∂μ otimesₘ κ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ otimesₘ κ) (μ
 otimesₘ η) p ∂(μ otimesₘ κ)
参数：h_ac : μ otimesₘ κ ≪ ν otimesₘ η；h_int : Integrable (llr (μ otimesₘ κ) (ν oti
mesₘ η)) (μ otimesₘ κ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_iff`：absolutelyConti
nuous_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFinit
eKernel η] [forall x, NeZero (κ x)] : μ otime…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `InformationTheory.integrable_llr_compProd_iff`：integrable_llr_compProd_i
ff (h_ac : μ otimesₘ κ ≪ ν otimesₘ η) : Integrable (llr (μ otimesₘ κ) (ν otimesₘ
 η)) (μ otimesₘ κ) ↔ Integrable (ll…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.integrable_compProd_iff`：integrable_compProd_iff [
SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] {f : α × β -> 
E} (hf : AEStronglyMeasurable f (μ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.log`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.log (f x)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Chain rule for the integral of the log-likelihood ratio, under absolute continui
ty and
integrability assumptions.
-/
lemma integral_llr_compProd_eq_add (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  have h_int1 : Integrable (fun p ↦ log ((∂μ/∂ν) p.1).toReal) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    · simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
      Filter.eventually_true, integral_const, probReal_univ, smul_eq_mul, one_mul, true_and]
      rwa [← integrable_norm_iff (by fun_prop)] at h_int_μν
    · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  calc ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η) := by
    rw [integral_rnDeriv_mul_log h_ac]
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
      (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η) :=
    integral_congr_ae (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)
  _ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ) :=
    integral_rnDeriv_smul h_ac
  _ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) +
      ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ) := by
    rw [integral_add h_int1]
    exact h_int_κη.ofReal
  _ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
    congr
    rw [Measure.integral_compProd h_int1]
    simp [llr]

variable (μ ν κ) in
@[simp]
/-
**InformationTheory.klDiv_compProd_left** 是 Mathlib 中的一个引理，位于命名空间 `InformationTh
eory`。
形式化陈述：klDiv_compProd_left : klDiv (μ otimesₘ κ) (ν otimesₘ κ) = klDiv μ ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_eq_lintegral_klFun_of_ac`：klDiv_eq_lintegral_klF
un_of_ac (h_ac : μ ≪ ν) : klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x
).toReal) ∂ν
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_left_iff`：absolutely
Continuous_compProd_left_iff [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [forall
 a, NeZero (κ a)] : μ otimesₘ κ ≪ ν otimesₘ κ ↔ μ …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.rnDeriv_measure_compProd_left`：rnDeriv_measure_compPro
d_left (μ ν : Measure α) (κ : Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν
] [IsFiniteKernel κ] : (μ otimesₘ κ).…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `InformationTheory.measurable_klFun`：measurable_klFun : Measurable klFun
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 34 条，此处仅展示前 30 条）
-/
lemma klDiv_compProd_left : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν := by
  -- first, if we don't have absolute continuity, both sides are `∞`
  by_cases h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ κ
  swap
  · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
    rwa [Measure.absolutelyContinuous_compProd_left_iff] at h_ac
  -- we can now express the KL divergences with an integral of a log-likelihood ratio
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac,
    klDiv_eq_lintegral_klFun_of_ac (Measure.absolutelyContinuous_compProd_left_iff.mp h_ac)]
  rw [Measure.absolutelyContinuous_compProd_left_iff] at h_ac
  calc ∫⁻ p, ENNReal.ofReal (klFun ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) p).toReal) ∂(ν ⊗ₘ κ)
  _ = ∫⁻ p, ENNReal.ofReal (klFun ((∂μ/∂ν) p.1).toReal) ∂(ν ⊗ₘ κ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [rnDeriv_measure_compProd_left μ ν κ] with p hp using by simp_rw [hp]
  _ = ∫⁻ x, ENNReal.ofReal (klFun ((∂μ/∂ν) x).toReal) ∂ν := by
    rw [Measure.lintegral_compProd (by fun_prop)]
    simp

variable (μ ν κ η) in
/-- **Chain rule** for the Kullback-Leibler divergence, with conditional KL expressed using
composition-products.
This version holds without any assumption on the measurable spaces. -/
/-
**InformationTheory.klDiv_compProd_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Information
Theory`。
形式化陈述：klDiv_compProd_eq_add : klDiv (μ otimesₘ κ) (ν otimesₘ η) = klDiv μ ν + kl
Div (μ otimesₘ κ) (μ otimesₘ η)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_iff`：absolutelyConti
nuous_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFinit
eKernel η] [forall x, NeZero (κ x)] : μ otime…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `InformationTheory.integrable_llr_compProd_iff`：integrable_llr_compProd_i
ff (h_ac : μ otimesₘ κ ≪ ν otimesₘ η) : Integrable (llr (μ otimesₘ κ) (ν otimesₘ
 η)) (μ otimesₘ κ) ↔ Integrable (ll…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_of_ac_of_integrable`：klDiv_of_ac_of_integrable (
h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) : klDiv μ ν = ENNReal.ofReal (∫ x, llr
 μ ν x ∂μ + ν.real univ - μ.real …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用引理 `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`：integral_llr
_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : 0 
<= ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply_univ`：compProd_apply_univ [SFinite 
μ] [IsMarkovKernel κ] : (μ otimesₘ κ) univ = μ univ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用引理 `InformationTheory.integral_llr_compProd_eq_add`：integral_llr_compProd_eq
_add (h_ac : μ otimesₘ κ ≪ ν otimesₘ η) (h_int : Integrable (llr (μ otimesₘ κ) (
ν otimesₘ η)) (μ otimesₘ κ)) : ∫ p, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
**Chain rule** for the Kullback-Leibler divergence, with conditional KL expresse
d using
composition-products.
This version holds without any assumption on the measurable spaces.
-/
theorem klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
  -- first, if we don't have absolute continuity, both sides are `∞`
  by_cases h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac h_ac]
    rw [Measure.absolutelyContinuous_compProd_iff] at h_ac
    simp only [not_and_or] at h_ac
    cases h_ac with
    | inl h => simp [h]
    | inr h => simp [h]
  -- same if we don't have integrability
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · rw [klDiv_of_not_integrable h_int]
    rw [integrable_llr_compProd_iff h_ac] at h_int
    simp only [not_and_or] at h_int
    cases h_int with
    | inl h => simp [h]
    | inr h => simp [h]
  -- now we can use express the KL divergences with an integral of a log-likelihood ratio
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  simp_rw [klDiv_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac_μν h_int_μν,
    klDiv_of_ac_of_integrable h_ac_κη h_int_κη,
    ← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg h_ac_μν h_int_μν)
    (integral_llr_add_sub_measure_univ_nonneg h_ac_κη h_int_κη), measureReal_def,
    Measure.compProd_apply_univ, add_sub_cancel_right]
  -- it suffices to prove the chain rule for the integrals of log-likelihood ratios
  suffices ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) by rw [this]; ring_nf
  -- the result follows from a previous lemma
  exact integral_llr_compProd_eq_add h_ac h_int

end InformationTheory

