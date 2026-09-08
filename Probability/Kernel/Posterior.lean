/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Deterministic

/-!

# Posterior kernel

For `μ : Measure Ω` (called prior measure), seen as a measure on a parameter, and a kernel
`κ : Kernel Ω 𝓧` that gives the conditional distribution of "data" in `𝓧` given the prior parameter,
we can get the distribution of the data with `κ ∘ₘ μ`, and the joint distribution of parameter and
data with `μ ⊗ₘ κ : Measure (Ω × 𝓧)`.

The posterior distribution of the parameter given the data is a Markov kernel `κ†μ : Kernel 𝓧 Ω`
such that `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`. That is, the joint distribution of parameter
and data can be recovered from the distribution of the data and the posterior.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`.

## Main statements

* `compProd_posterior_eq_map_swap`: the main property of the posterior,
  `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`.
* `ae_eq_posterior_of_compProd_eq`
* `posterior_comp_self`: `κ†μ ∘ₘ κ ∘ₘ μ = μ`
* `posterior_posterior`: `(κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ`
* `posterior_comp`: `(η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ)`

* `posterior_eq_withDensity`: If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`,
  then for `κ ∘ₘ μ`-almost every `x`,
  `κ†μ x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
  The condition is true for countable `Ω`: see `absolutelyContinuous_comp_of_countable`.

## Notation

`κ†μ` denotes the posterior of `κ` with respect to `μ`, `posterior κ μ`.
`†` can be typed as `\dag` or `\dagger`.

This notation emphasizes that the posterior is a kind of inverse of `κ`, which we would want to
denote `κ†`, but we have to also specify the measure `μ`.

-/

@[expose] public section

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
    {κ : Kernel Ω 𝓧} {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteKernel κ]

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
/-
**ProbabilityTheory.posterior** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：posterior (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKe
rnel κ] : Kernel 𝓧 Ω
参数：κ : Kernel Ω 𝓧；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def posterior (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    Kernel 𝓧 Ω :=
  ((μ ⊗ₘ κ).map Prod.swap).condKernel

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
scoped[ProbabilityTheory] infix:arg "†" => ProbabilityTheory.posterior

/-- The posterior is a Markov kernel. -/
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The posterior is a Markov kernel.
-/
instance : IsMarkovKernel κ†μ := by rw [posterior]; infer_instance

/-- The main property of the posterior. -/
/-
**ProbabilityTheory.compProd_posterior_eq_map_swap** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：compProd_posterior_eq_map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map 
Prod.swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.fst_map_swap`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory.Measure
 (α × β)}, (MeasureTheor…
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…

--- 原说明 ---
The main property of the posterior.
-/
lemma compProd_posterior_eq_map_swap : (κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap := by
  simpa using! ((μ ⊗ₘ κ).map Prod.swap).disintegrate ((μ ⊗ₘ κ).map Prod.swap).condKernel
/-
**ProbabilityTheory.compProd_posterior_eq_swap_comp** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：compProd_posterior_eq_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘
ₘ μ otimesₘ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_map_swap`：compProd_posterior_eq_
map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap
· 使用引理 `MeasureTheory.Measure.swap_comp`：swap_comp {μ : Measure (α × β)} : (Kern
el.swap α β) ∘ₘ μ = μ.map Prod.swap
-/
lemma compProd_posterior_eq_swap_comp : (κ ∘ₘ μ) ⊗ₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_map_swap, Measure.swap_comp]
/-
**ProbabilityTheory.swap_compProd_posterior** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：swap_compProd_posterior : Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otim
esₘ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_swap_comp`：compProd_posterior_eq
_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.swap_swap`：swap_swap : (swap α β) ∘ₖ (swap β α)
 = Kernel.id
· 使用引理 `MeasureTheory.Measure.id_comp`：id_comp : Kernel.id ∘ₘ μ = μ
-/
lemma swap_compProd_posterior : Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) ⊗ₘ κ†μ = μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_swap_comp, Measure.comp_assoc, Kernel.swap_swap, Measure.id_comp]

/-- The main property of the posterior, as equality of the following diagrams:
```
         -- id          -- κ
μ -- κ -|        =  μ -|
         -- κ†μ         -- id
``` -/
/-
**ProbabilityTheory.parallelProd_posterior_comp_copy_comp** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：parallelProd_posterior_comp_copy_comp : (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 
𝓧 ∘ₘ κ ∘ₘ μ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_eq_parallelComp_comp_copy_comp`：compProd_
eq_parallelComp_comp_copy_comp [SFinite μ] : μ otimesₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ K
ernel.copy α ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_swap_comp`：compProd_posterior_eq
_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.swap_parallelComp`：swap_parallelComp : swap Y T
 ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用引理 `ProbabilityTheory.Kernel.swap_copy`：swap_copy : (swap α α) ∘ₖ (copy α) =
 copy α

--- 原说明 ---
The main property of the posterior, as equality of the following diagrams:
```
         -- id          -- κ
μ -- κ -|        =  μ -|
         -- κ†μ         -- id
```
-/
lemma parallelProd_posterior_comp_copy_comp :
    (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
      = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) ⊗ₘ κ†μ := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_posterior_eq_swap_comp]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.swap_parallelComp, Measure.comp_assoc, Kernel.comp_assoc,
      Kernel.swap_copy, Measure.comp_assoc]
/-
**ProbabilityTheory.posterior_prod_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：posterior_prod_id_comp : (κ†μ ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ otimesₘ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.swap_prod`：swap_prod {κ : Kernel α β} [IsSFinit
eKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] : (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ
 κ)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_swap_comp`：compProd_posterior_eq
_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
· 使用引理 `ProbabilityTheory.Kernel.swap_swap`：swap_swap : (swap α β) ∘ₖ (swap β α)
 = Kernel.id
· 使用引理 `MeasureTheory.Measure.id_comp`：id_comp : Kernel.id ∘ₘ μ = μ
-/
lemma posterior_prod_id_comp : (κ†μ ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ ⊗ₘ κ := by
  rw [← Kernel.swap_prod, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    compProd_posterior_eq_swap_comp, Measure.comp_assoc, Kernel.swap_swap, Measure.id_comp]

/-- The posterior is unique up to a `κ ∘ₘ μ`-null set. -/
/-
**ProbabilityTheory.ae_eq_posterior_of_compProd_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：ae_eq_posterior_of_compProd_eq {η : Kernel 𝓧 Ω} [IsFiniteKernel η] (h : (κ
 ∘ₘ μ) otimesₘ η = (μ otimesₘ κ).map Prod.swap) : η =ᵐ[κ ∘ₘ μ] κ†μ
参数：h : (κ ∘ₘ μ) otimesₘ η = (μ otimesₘ κ).map Prod.swap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`：ae_eq_of_compProd_eq [IsF
initeMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (h : μ otimesₘ κ = μ otime
sₘ η) : κ =ᵐ[μ] η
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_map_swap`：compProd_posterior_eq_
map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The posterior is unique up to a `κ ∘ₘ μ`-null set.
-/
lemma ae_eq_posterior_of_compProd_eq {η : Kernel 𝓧 Ω} [IsFiniteKernel η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  (Kernel.ae_eq_of_compProd_eq (compProd_posterior_eq_map_swap.trans h.symm)).symm

/-- The posterior is unique up to a `κ ∘ₘ μ`-null set. -/
/-
**ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：ae_eq_posterior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel 
η] (h : ((κ ∘ₘ μ) otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ) : η =ᵐ[κ ∘ₘ μ] κ†
μ
参数：η : Kernel 𝓧 Ω；h : ((κ ∘ₘ μ) otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.ae_eq_posterior_of_compProd_eq`：ae_eq_posterior_of_com
pProd_eq {η : Kernel 𝓧 Ω} [IsFiniteKernel η] (h : (κ ∘ₘ μ) otimesₘ η = (μ otimes
ₘ κ).map Prod.swap) : η =ᵐ[κ ∘ₘ μ] κ†μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.swap_comp`：swap_comp {μ : Measure (α × β)} : (Kern
el.swap α β) ∘ₘ μ = μ.map Prod.swap

--- 原说明 ---
The posterior is unique up to a `κ ∘ₘ μ`-null set.
-/
lemma ae_eq_posterior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  ae_eq_posterior_of_compProd_eq <| by rw [h, Measure.swap_comp]

@[simp]
/-
**ProbabilityTheory.posterior_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：posterior_comp_self [IsMarkovKernel κ] : κ†μ ∘ₘ κ ∘ₘ μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
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
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_map_swap`：compProd_posterior_eq_
map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap
· 使用定理 `MeasureTheory.Measure.snd_map_swap`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory.Measure
 (α × β)}, (MeasureTheor…
· 使用引理 `MeasureTheory.Measure.fst_compProd`：fst_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsMarkovKernel κ] : (μ otimesₘ κ).fst = μ
-/
lemma posterior_comp_self [IsMarkovKernel κ] : κ†μ ∘ₘ κ ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap, Measure.snd_map_swap,
    Measure.fst_compProd]

/-- The posterior of the identity kernel is the identity kernel. -/
/-
**ProbabilityTheory.posterior_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：posterior_id (μ : Measure Ω) [IsFiniteMeasure μ] : Kernel.id†μ =ᵐ[μ] Kerne
l.id
参数：μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用引理 `ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp`：ae_eq_poster
ior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel η] (h : ((κ ∘ₘ μ) 
otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ) : η…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.id_comp`：id_comp : Kernel.id ∘ₘ μ = μ
· 使用引理 `MeasureTheory.Measure.compProd_id_eq_copy_comp`：compProd_id_eq_copy_comp
 [SFinite μ] : μ otimesₘ Kernel.id = Kernel.copy α ∘ₘ μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.swap_copy`：swap_copy : (swap α α) ∘ₖ (copy α) =
 copy α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The posterior of the identity kernel is the identity kernel.
-/
lemma posterior_id (μ : Measure Ω) [IsFiniteMeasure μ] : Kernel.id†μ =ᵐ[μ] Kernel.id := by
  suffices Kernel.id =ᵐ[Kernel.id ∘ₘ μ] (Kernel.id : Kernel Ω Ω)†μ by
    rw [Measure.id_comp] at this
    filter_upwards [this] with a ha using ha.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp Kernel.id ?_
  rw [Measure.id_comp, Measure.compProd_id_eq_copy_comp, Measure.comp_assoc, Kernel.swap_copy]

/-- For a deterministic kernel `κ`, `κ ∘ₖ κ†μ` is `μ.map f`-a.e. equal to the identity kernel. -/
/-
**ProbabilityTheory.deterministic_comp_posterior** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：deterministic_comp_posterior [MeasurableSpace.CountablyGenerated 𝓧] {f : Ω
 -> 𝓧} (hf : Measurable f) : Kernel.deterministic f hf ∘ₖ (Kernel.deterministic 
f hf)†μ =ᵐ[μ.map f] Kernel.id
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`：ae_eq_of_compProd_eq [IsF
initeMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (h : μ otimesₘ κ = μ otime
sₘ η) : κ =ᵐ[μ] η
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用引理 `MeasureTheory.Measure.compProd_eq_parallelComp_comp_copy_comp`：compProd_
eq_parallelComp_comp_copy_comp [SFinite μ] : μ otimesₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ K
ernel.copy α ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp`：paralle
lComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kerne
l Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥…
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.parallelProd_posterior_comp_copy_comp`：parallelProd_po
sterior_comp_copy_comp : (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ = (κ ∥ₖ K
ernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_parallelComp`：parallelComp_co
mp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η] {κ' : K
ernel X' Y'} [IsSFiniteKernel κ'] {η' : Kerne…
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_self_comp_copy`：parallelComp_self_
comp_copy {κ : Kernel α β} [IsDeterministic κ] : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Ker
nel.copy β ∘ₖ κ
· 使用定理 `ProbabilityTheory.Kernel.instIsDeterministicDeterministic`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β}
 (hf : Measurable f),   ProbabilityTheory.IsDet…
· 使用引理 `MeasureTheory.Measure.compProd_id_eq_copy_comp`：compProd_id_eq_copy_comp
 [SFinite μ] : μ otimesₘ Kernel.id = Kernel.copy α ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…

--- 原说明 ---
For a deterministic kernel `κ`, `κ ∘ₖ κ†μ` is `μ.map f`-a.e. equal to the identi
ty kernel.
-/
lemma deterministic_comp_posterior [MeasurableSpace.CountablyGenerated 𝓧]
    {f : Ω → 𝓧} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ =ᵐ[μ.map f] Kernel.id := by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f ⊗ₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ)
  _ = (Kernel.deterministic f hf ∘ₘ μ)
      ⊗ₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ) := by
    rw [Measure.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ (Kernel.deterministic f hf)†μ) ∘ₘ
      Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp,
      ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy Ω ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.parallelComp_comp_parallelComp, Kernel.id_comp, Kernel.comp_id]
  _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    rw [Measure.comp_assoc, Kernel.parallelComp_self_comp_copy]
  _ = μ.map f ⊗ₘ Kernel.id := by
    rw [Measure.compProd_id_eq_copy_comp, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map]
/-
**ProbabilityTheory.absolutelyContinuous_posterior** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：absolutelyContinuous_posterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ
 ω ∂μ, κ ω ≪ ν) : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
参数：h_ac : forallᵐ ω ∂μ, κ ω ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_const`：compProd_const {ν : Measure β} [SF
inite μ] [SFinite ν] : μ otimesₘ (Kernel.const α ν) = μ.prod ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_right`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measur
eTheory.Measure α}   {κ η : ProbabilityTheory.K…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_map_swap`：compProd_posterior_eq_
map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : 
MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma absolutelyContinuous_posterior {ν : Measure 𝓧} [SFinite ν] (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν) :
    ∀ᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ := by
  suffices (κ ∘ₘ μ) ⊗ₘ (κ†μ) ≪ ν.prod μ by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices μ ⊗ₘ κ ≪ μ.prod ν by
    rw [compProd_posterior_eq_map_swap, ← Measure.prod_swap]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

section StandardBorelSpace

variable [StandardBorelSpace 𝓧] [Nonempty 𝓧]

/-- The posterior is involutive (up to `μ`-a.e. equality). -/
/-
**ProbabilityTheory.posterior_posterior** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：posterior_posterior [IsMarkovKernel κ] : (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用引理 `ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp`：ae_eq_poster
ior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel η] (h : ((κ ∘ₘ μ) 
otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ) : η…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.posterior_comp_self`：posterior_comp_self [IsMarkovKern
el κ] : κ†μ ∘ₘ κ ∘ₘ μ = μ
· 使用引理 `ProbabilityTheory.compProd_posterior_eq_swap_comp`：compProd_posterior_eq
_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.swap_swap`：swap_swap : (swap α β) ∘ₖ (swap β α)
 = Kernel.id
· 使用引理 `MeasureTheory.Measure.id_comp`：id_comp : Kernel.id ∘ₘ μ = μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The posterior is involutive (up to `μ`-a.e. equality).
-/
lemma posterior_posterior [IsMarkovKernel κ] : (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ := by
  suffices κ =ᵐ[κ†μ ∘ₘ κ ∘ₘ μ] (κ†μ)†(κ ∘ₘ μ) by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp κ ?_
  rw [posterior_comp_self, compProd_posterior_eq_swap_comp, Measure.comp_assoc,
    Kernel.swap_swap, Measure.id_comp]

/-- The posterior is contravariant. -/
/-
**ProbabilityTheory.posterior_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：posterior_comp {η : Kernel 𝓧 𝓨} [IsFiniteKernel η] : (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ 
∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp`：ae_eq_poster
ior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel η] (h : ((κ ∘ₘ μ) 
otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ) : η…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.parallelProd_posterior_comp_copy_comp`：parallelProd_po
sterior_comp_copy_comp : (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ = (κ ∥ₖ K
ernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comm`：parallelComp_comm : (Kernel.
id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用引理 `ProbabilityTheory.Kernel.swap_parallelComp`：swap_parallelComp : swap Y T
 ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
· 使用引理 `ProbabilityTheory.Kernel.swap_copy`：swap_copy : (swap α α) ∘ₖ (copy α) =
 copy α

--- 原说明 ---
The posterior is contravariant.
-/
lemma posterior_comp {η : Kernel 𝓧 𝓨} [IsFiniteKernel η] :
    (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ) := by
  rw [Measure.comp_assoc]
  refine (ae_eq_posterior_of_compProd_eq_swap_comp ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_).symm
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ (Kernel.copy 𝓨) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [Measure.comp_assoc, Kernel.parallelComp_comm, ← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp, Kernel.comp_assoc, ← Kernel.comp_assoc (Kernel.swap Ω 𝓧),
      Kernel.swap_parallelComp, Kernel.comp_assoc, Kernel.swap_copy]

end StandardBorelSpace


section CountableOrCountablyGenerated

variable [MeasurableSpace.CountableOrCountablyGenerated Ω 𝓧]

/-
**ProbabilityTheory.absolutelyContinuous_of_posterior** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：absolutelyContinuous_of_posterior (h_ac : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
) : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
参数：h_ac : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_const`：compProd_const {ν : Measure β} [SF
inite μ] [SFinite ν] : μ otimesₘ (Kernel.const α ν) = μ.prod ν
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_right`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measur
eTheory.Measure α}   {κ η : ProbabilityTheory.K…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用引理 `ProbabilityTheory.swap_compProd_posterior`：swap_compProd_posterior : Ker
nel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otimesₘ κ
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用引理 `MeasureTheory.Measure.swap_comp`：swap_comp {μ : Measure (α × β)} : (Kern
el.swap α β) ∘ₘ μ = μ.map Prod.swap
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : 
MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
-/
lemma absolutelyContinuous_of_posterior (h_ac : ∀ᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  suffices μ ⊗ₘ κ ≪ μ.prod (κ ∘ₘ μ) by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices (κ ∘ₘ μ) ⊗ₘ κ†μ ≪ (κ ∘ₘ μ).prod μ by
    rw [← swap_compProd_posterior, ← Measure.prod_swap, Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa
/-
**ProbabilityTheory.absolutelyContinuous_posterior_iff** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：absolutelyContinuous_posterior_iff : (forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ 
forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.absolutelyContinuous_of_posterior`：absolutelyContinuou
s_of_posterior (h_ac : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) : forallᵐ ω ∂μ, κ ω ≪ κ
 ∘ₘ μ
· 使用引理 `ProbabilityTheory.absolutelyContinuous_posterior`：absolutelyContinuous_p
osterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) : forallᵐ b 
∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma absolutelyContinuous_posterior_iff : (∀ᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  ⟨absolutelyContinuous_of_posterior, absolutelyContinuous_posterior⟩
/-
**ProbabilityTheory.Kernel.absolutelyContinuous_comp_of_absolutelyContinuous** 是
 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {κ : ProbabilityTheory.Kernel Ω 𝓧}   {μ : MeasureTheory.Measure Ω} [Meas
ureTheory.IsFiniteMeasure μ] [ProbabilityTheory.IsFiniteKernel κ]   [StandardBor
elSpace Ω] [Nonempty Ω] [MeasurableSpace.CountableOrCountablyGenerated Ω 𝓧] {ν :
 MeasureTheory.Measure 𝓧}   [MeasureTheory.SFinite ν],   (∀ᵐ (ω : Ω) ∂μ, (κ ω).A
bsolutelyContinuous ν) → ∀ᵐ (ω : Ω) ∂μ, (κ ω).AbsolutelyContinuous (μ.bind ⇑κ)
参数：∀ᵐ (ω : Ω) ∂μ, (κ ω).AbsolutelyContinuous ν；ω : Ω；κ ω；μ.bind ⇑κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.absolutelyContinuous_posterior_iff`：absolutelyContinuo
us_posterior_iff : (forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ
 μ
· 使用引理 `ProbabilityTheory.absolutelyContinuous_posterior`：absolutelyContinuous_p
osterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) : forallᵐ b 
∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
-/
lemma Kernel.absolutelyContinuous_comp_of_absolutelyContinuous {ν : Measure 𝓧} [SFinite ν]
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  rw [← absolutelyContinuous_posterior_iff]
  exact absolutelyContinuous_posterior h_ac
/-
**ProbabilityTheory.rnDeriv_posterior_ae_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：rnDeriv_posterior_ae_prod (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ p 
∂(μ.prod (κ ∘ₘ μ)), (κ†μ).rnDeriv (Kernel.const _ μ) p.2 p.1 = κ.rnDeriv (Kernel
.const _ (κ ∘ₘ μ)) p.1 p.2
参数：h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_prod_symm`：setLIntegral_prod_symm [SFinite μ]
 {s : Set α} {t : Set β} (f : α × β -> Real>=0∞) (hf : AEMeasurable f ((μ.prod ν
).restrict (s ×ˢ t))) : ∫⁻…
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.swap_compProd_posterior`：swap_compProd_posterior : Ker
nel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otimesₘ κ
· 使用引理 `MeasureTheory.Measure.swap_comp`：swap_comp {μ : Measure (α × β)} : (Kern
el.swap α β) ∘ₘ μ = μ.map Prod.swap
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.preimage_swap_prod`：preimage_swap_prod (s : Set α) (t : Set β) : Pro
d.swap ⁻¹' s ×ˢ t = t ×ˢ s
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.absolutelyContinuous_posterior`：absolutelyContinuous_p
osterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) : forallᵐ b 
∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 42 条，此处仅展示前 30 条）
-/
lemma rnDeriv_posterior_ae_prod (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ p ∂(μ.prod (κ ∘ₘ μ)),
      (κ†μ).rnDeriv (Kernel.const _ μ) p.2 p.1 = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) p.1 p.2 := by
  -- We prove the a.e. equality by showing that integrals on the π-system of rectangles are equal.
  -- First, the integral of the left-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`, which we prove
  -- by showing that it's equal to `((κ ∘ₘ μ) ⊗ κ†μ) (t ×ˢ s)` and using the main property of the
  -- posterior.
  have h1 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫⁻ x in s ×ˢ t, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ ⊗ₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod_symm _ (by fun_prop), ← swap_compProd_posterior, Measure.swap_comp,
      Measure.map_apply measurable_swap (hs.prod ht), Set.preimage_swap_prod,
      Measure.compProd_apply_prod ht hs]
    refine lintegral_congr_ae <| ae_restrict_of_ae ?_
    filter_upwards [absolutelyContinuous_posterior h_ac] with x h_ac'
    change ∫⁻ ω in s, (κ†μ).rnDeriv (Kernel.const 𝓧 μ) x ω ∂(Kernel.const 𝓧 μ x) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac' hs]
  have h2 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
  -- Second, the integral of the right-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`.
      ∫⁻ x in s ×ˢ t, κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) x.1 x.2 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ ⊗ₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod _ (by fun_prop), Measure.compProd_apply_prod hs ht]
    refine lintegral_congr_ae <| ae_restrict_of_ae ?_
    filter_upwards [h_ac] with ω h_ac
    change ∫⁻ x in t, κ.rnDeriv (Kernel.const Ω (κ ∘ₘ μ)) ω x ∂(Kernel.const Ω (κ ∘ₘ μ) ω) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac ht]
  -- We extend from the π-system to the σ-algebra.
  refine ae_eq_of_setLIntegral_prod_eq (by fun_prop) (by fun_prop) ?_ ?_
  · refine ne_of_lt ?_
    calc ∫⁻ x, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (κ ∘ₘ μ)
    _ = (μ ⊗ₘ κ) Set.univ := by rw [← setLIntegral_univ, ← Set.univ_prod_univ, h1 .univ .univ]
    _ < ⊤ := measure_lt_top _ _
  · intro s hs t ht
    rw [h1 hs ht, h2 hs ht]
/-
**ProbabilityTheory.rnDeriv_posterior** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：rnDeriv_posterior (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ ω ∂μ, fora
llᵐ x ∂(κ ∘ₘ μ), (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const 
_ (κ ∘ₘ μ)) ω x
参数：h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.rnDeriv_posterior_ae_prod`：rnDeriv_posterior_ae_prod (
h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ p ∂(μ.prod (κ ∘ₘ μ)), (κ†μ).rnDeriv
 (Kernel.const _ μ) p.2 p.1 = κ.r…
-/
lemma rnDeriv_posterior (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂(κ ∘ₘ μ),
      (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  convert!
    Measure.ae_ae_of_ae_prod
      (rnDeriv_posterior_ae_prod h_ac) -- much faster than `exact`
         -- much faster than `exact`
/-
**ProbabilityTheory.rnDeriv_posterior_symm** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：rnDeriv_posterior_symm (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ x ∂(κ
 ∘ₘ μ), forallᵐ ω ∂μ, (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.c
onst _ (κ ∘ₘ μ)) ω x
参数：h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ae_ae_comm`：ae_ae_comm {p : α -> β -> Prop} (h : M
easurableSet {x : α × β | p x.1 x.2}) : (forallᵐ x ∂μ, forallᵐ y ∂ν, p x y) ↔ fo
rallᵐ y ∂ν, forallᵐ x …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Measurable.eq`：Measurable.eq {m : MeasurableSpace α} [MeasurableSpace β]
 [MeasurableEq β] {f g : α -> β} (hf : Measurable f) (hg : Measurable g) : Measu
rab…
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用引理 `ProbabilityTheory.rnDeriv_posterior`：rnDeriv_posterior (h_ac : forallᵐ ω
 ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ ω ∂μ, forallᵐ x ∂(κ ∘ₘ μ), (κ†μ).rnDeriv (Kernel.co
nst _ μ) x ω = κ.rnDeriv …
-/
lemma rnDeriv_posterior_symm (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), ∀ᵐ ω ∂μ,
      (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  rw [Measure.ae_ae_comm]
  · exact rnDeriv_posterior h_ac
  · measurability

/-- If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, then for `κ ∘ₘ μ`-almost every `x`,
`κ†μ x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
This is a form of **Bayes' theorem**.
The condition is true for example for countable `Ω`. -/
/-
**ProbabilityTheory.posterior_eq_withDensity** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：posterior_eq_withDensity (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ x ∂
(κ ∘ₘ μ), (κ†μ) x = μ.withDensity (fun ω => κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) 
ω x)
参数：h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.absolutelyContinuous_posterior`：absolutelyContinuous_p
osterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) : forallᵐ b 
∂(κ ∘ₘ μ), (κ†μ) b ≪ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用引理 `ProbabilityTheory.rnDeriv_posterior_symm`：rnDeriv_posterior_symm (h_ac :
 forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ x ∂(κ ∘ₘ μ), forallᵐ ω ∂μ, (κ†μ).rnDeriv 
(Kernel.const _ μ) x ω = κ.rnD…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv`：setLIntegral_rnDeriv [HaveLe
besgueDecomposition μ ν] [SFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫⁻ x in s, μ.rn
Deriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ

--- 原说明 ---
If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, then for `κ ∘ₘ μ`-almost every `x`,
`κ†μ x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
This is a form of **Bayes' theorem**.
The condition is true for example for countable `Ω`.
-/
lemma posterior_eq_withDensity (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x) := by
  filter_upwards [rnDeriv_posterior_symm h_ac, absolutelyContinuous_posterior h_ac] with x h h_ac'
  ext s hs
  rw [← Measure.setLIntegral_rnDeriv h_ac', withDensity_apply _ hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [h, Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ†μ) (η := Kernel.const 𝓧 μ) (a := x)]
    with ω h h_eq hωs
  rw [← h, h_eq, Kernel.const_apply]
/-
**ProbabilityTheory.posterior_eq_withDensity_of_countable** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：posterior_eq_withDensity_of_countable {Ω : Type*} [Countable Ω] [Measurabl
eSpace Ω] [Nonempty Ω] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [IsFiniteKernel κ
] (μ : Measure Ω) [IsFiniteMeasure μ] : forallᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDen
sity (fun ω => (κ ω).rnDeriv (κ ∘ₘ μ) x)
参数：κ : Kernel Ω 𝓧；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用引理 `ProbabilityTheory.posterior_eq_withDensity`：posterior_eq_withDensity (h_
ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) : forallᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDensity 
(fun ω => κ.rnDeriv (Kernel.cons…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_comp_of_countable`：absolutely
Continuous_comp_of_countable [Countable α] [MeasurableSingletonClass α] : forall
ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posterior_eq_withDensity_of_countable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [Nonempty Ω] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDensity (fun ω ↦ (κ ω).rnDeriv (κ ∘ₘ μ) x) := by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

end CountableOrCountablyGenerated

section Bool

/-
**ProbabilityTheory.posterior_boolKernel_apply_false** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：posterior_boolKernel_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [Is
FiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] : forallᵐ x ∂Kernel.bool
Kernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {false} = π {false} * μ.rnDeriv (
Kernel.boolKernel μ ν ∘ₘ π) x
参数：μ ν : Measure 𝓧；π : Measure Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelBoolBoolKernelOfIsFiniteMeasu
re`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [M
easureTheory.IsFiniteMeasure μ]   [MeasureTheory.IsFiniteMeasure…
· 使用引理 `ProbabilityTheory.posterior_eq_withDensity_of_countable`：posterior_eq_wi
thDensity_of_countable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [Nonempty Ω
] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posterior_boolKernel_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {false}
      = π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp
/-
**ProbabilityTheory.posterior_boolKernel_apply_true** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：posterior_boolKernel_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsF
initeMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] : forallᵐ x ∂Kernel.boolK
ernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {true} = π {true} * ν.rnDeriv (Ker
nel.boolKernel μ ν ∘ₘ π) x
参数：μ ν : Measure 𝓧；π : Measure Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelBoolBoolKernelOfIsFiniteMeasu
re`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [M
easureTheory.IsFiniteMeasure μ]   [MeasureTheory.IsFiniteMeasure…
· 使用引理 `ProbabilityTheory.posterior_eq_withDensity_of_countable`：posterior_eq_wi
thDensity_of_countable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [Nonempty Ω
] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posterior_boolKernel_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {true}
      = π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

end Bool

end ProbabilityTheory

