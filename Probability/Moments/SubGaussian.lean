/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

/-!
# Sub-Gaussian random variables

This presentation of sub-Gaussian random variables is inspired by section 2.5 of
[vershynin2018high]. Let `X` be a random variable. Consider the following five properties, in which
`Kᵢ` are positive reals,
* (i) for all `t ≥ 0`, `ℙ(|X| ≥ t) ≤ 2 * exp(-t^2 / K₁^2)`,
* (ii) for all `p : ℕ` with `1 ≤ p`, `𝔼[|X|^p]^(1/p) ≤ K₂ sqrt(p)`,
* (iii) for all `|t| ≤ 1/K₃`, `𝔼[exp (t^2 * X^2)] ≤ exp (K₃^2 * t^2)`,
* (iv) `𝔼[exp(X^2 / K₄)] ≤ 2`,
* (v) for all `t : ℝ`, `𝔼[exp (t * X)] ≤ exp (K₅ * t^2 / 2)`.

Properties (i) to (iv) are equivalent, in the sense that there exists a constant `C` such that
if `X` satisfies one of those properties with constant `K`, then it satisfies any other one with
constant at most `CK`.

If `𝔼[X] = 0` then properties (i)-(iv) are equivalent to (v) in that same sense.
Property (v) implies that `X` has expectation zero.

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian moment-generating function (mgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `exp (K₅ * t^2 / 2)` which appears in
property (v) is the mgf of a Gaussian with variance `K₅`.
That property (v) is the most convenient one to work with if one wants to prove concentration
inequalities using Chernoff's method.

TODO: implement definitions for (i)-(iv) when it makes sense. For example the maximal constant `K₄`
such that (iv) is true is an Orlicz norm. Prove relations between those properties.

### Conditionally sub-Gaussian random variables and kernels

A related notion to sub-Gaussian random variables is that of conditionally sub-Gaussian random
variables. A random variable `X` is conditionally sub-Gaussian in the sense of (v) with respect to
a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the conditional mgf of `X` conditioned on `m` is almost surely bounded by `exp (c * t^2 / 2)`
for some constant `c`.

As in other parts of Mathlib's probability library (notably the independence and conditional
independence definitions), we express both sub-Gaussian and conditionally sub-Gaussian properties
as special cases of a notion of sub-Gaussianity with respect to a kernel and a measure.

## Main definitions

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment-generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment-generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.

## Main statements

* `measure_sum_ge_le_of_iIndepFun`: Hoeffding's inequality for sums of independent sub-Gaussian
  random variables.
* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: Hoeffding's lemma for random variables with
  expectation zero.
* `measure_sum_ge_le_of_HasCondSubgaussianMGF`: the Azuma-Hoeffding inequality for sub-Gaussian
  random variables.

## Implementation notes

### Definition of `Kernel.HasSubgaussianMGF`

The definition of sub-Gaussian with respect to a kernel and a measure is the following:
```
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)
```
An interesting point is that the integrability condition is not integrability of `exp (t * X)`
with respect to `κ ω'` for `ν`-almost all `ω'`, but integrability with respect to `κ ∘ₘ ν`.
This is a stronger condition, as the weaker one did not allow to prove interesting results about
the sum of two sub-Gaussian random variables.

For the conditional case, that integrability condition reduces to integrability of `exp (t * X)`
with respect to `μ`.

### Definition of `HasCondSubgaussianMGF`

We define `HasCondSubgaussianMGF` as a special case of `Kernel.HasSubgaussianMGF` with the
conditional expectation kernel for `m`, `condExpKernel μ m`, and the restriction of `μ` to `m`,
`μ.trim hm` (where `hm` states that `m` is a sub-sigma-algebra).
Note that `condExpKernel μ m ∘ₘ μ.trim hm = μ`. The definition is equivalent to the two
conditions
* for all `t`, `exp (t * X)` is `μ`-integrable,
* for `μ.trim hm`-almost all `ω`, for all `t`, the mgf with respect to the conditional
  distribution `condExpKernel μ m ω` is bounded by `exp (c * t ^ 2 / 2)`.

For any `t`, we can write the mgf of `X` with respect to the conditional expectation kernel as
a conditional expectation, `(μ.trim hm)`-almost surely:
`mgf X (condExpKernel μ m ·) t =ᵐ[μ.trim hm] μ[fun ω' ↦ exp (t * X ω') | m]`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
  science*][vershynin2018high]

-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

/-- A random variable `X` has a sub-Gaussian moment-generating function with parameter `c`
with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`, for all `t : ℝ`,
the moment-generating function of `X` with respect to `κ ω'` is bounded by `exp (c * t ^ 2 / 2)`.
This implies in particular that `X` has expectation 0. -/
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：{Ω : Type u_1} →   {Ω' : Type u_2} →     {mΩ : MeasurableSpace Ω} →       
{mΩ' : MeasurableSpace Ω'} →         (Ω → ℝ) →           NNReal →             Pr
obabilityTheory.Kernel Ω' Ω →               autoParam (MeasureTheory.Measure Ω')
 ProbabilityTheory.Kernel.HasSubgaussianMGF._auto_1 → Prop
参数：Ω → ℝ；MeasureTheory.Measure Ω'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X` has a sub-Gaussian moment-generating function with paramet
er `c`
with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`, for a
ll `t : ℝ`,
the moment-generating function of `X` with respect to `κ ω'` is bounded by `exp 
(c * t ^ 2 / 2)`.
This implies in particular that `X` has expectation 0.
-/
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

namespace Kernel.HasSubgaussianMGF

section BasicProperties

/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.aestronglyMeasurable** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) : AEStronglyMeasurabl
e X (κ ∘ₘ ν)
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_integrable_exp_mul** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) : forallᵐ
 ω' ∂ν, Integrable (fun y => exp (t * X y)) (κ ω')
参数：h : HasSubgaussianMGF X c κ ν；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.ae_integrable_of_integrable_comp`：ae_integrable_of
_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) : forallᵐ x ∂μ, Integrable f (κ
 x)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
-/
lemma ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_aestronglyMeasurable** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, A
EStronglyMeasurable X (κ ω')
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_integrable_exp_mul`：ae_int
egrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) : forallᵐ ω' ∂ν, Inte
grable (fun y => exp (t * X y)) (κ ω')
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma ae_aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  have h_int := h.ae_integrable_exp_mul 1
  filter_upwards [h_int] with ω h_int
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul** 是 Ma
thlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' 
∂ν, forall t, Integrable (fun ω => exp (t * X ω)) (κ ω')
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_integrable_exp_mul`：ae_int
egrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) : forallᵐ ω' ∂ν, Inte
grable (fun y => exp (t * X y)) (κ ω')
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
-/
lemma ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have h_int (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_memLp_exp_mul** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_forall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : Real>=0) : fo
rallᵐ ω' ∂ν, forall t, MemLp (fun ω => exp (t * X ω)) p (κ ω')
参数：h : HasSubgaussianMGF X c κ ν；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul`
：ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, f
orall t, Integrable (fun ω => exp (t * X ω)) (κ ω')
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r
· 使用定理 `MeasureTheory.Integrable.lintegral_lt_top`：∀ {α : Type u_1} {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrab
le f μ → ∫⁻ (x : α), ENNReal.of…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma ae_forall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : ℝ≥0) :
    ∀ᵐ ω' ∂ν, ∀ t, MemLp (fun ω ↦ exp (t * X ω)) p (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp),
      ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert! hf using 3 with ω
    rw [enorm_eq_ofReal (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity),
      ← exp_mul, mul_comm, ← mul_assoc]
    positivity
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.memLp_exp_mul** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) : M
emLp (fun ω => exp (t * X ω)) p (κ ∘ₘ ν)
参数：h : HasSubgaussianMGF X c κ ν；t : Real；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MeasureTheory.hasFiniteIntegral_def`：hasFiniteIntegral_def {_ : Measurab
leSpace α} (f : α -> ε) (μ : Measure α) : HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ 
∂μ < ∞)
-/
lemma memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert! h' using 3 with ω
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
    positivity
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.cgf_le** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：cgf_le (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, forall t, cgf X (κ
 ω') t <= c * t ^ 2 / 2
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul`
：ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, f
orall t, Integrable (fun ω => exp (t * X ω)) (κ ω')
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
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
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
（共 32 条，此处仅展示前 30 条）
-/
lemma cgf_le (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ ≤ c * t ^ 2 / 2 := by rw [log_exp]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.isFiniteMeasure** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：isFiniteMeasure (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, IsFiniteM
easure (κ ω')
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_integrable_exp_mul`：ae_int
egrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) : forallᵐ ω' ∂ν, Inte
grable (fun y => exp (t * X y)) (κ ω')
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma isFiniteMeasure (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, IsFiniteMeasure (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_univ_le_one** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：measure_univ_le_one (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, κ ω' 
Set.univ <= 1
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.isFiniteMeasure`：isFiniteMeas
ure (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, IsFiniteMeasure (κ ω')
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma measure_univ_le_one (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, κ ω' Set.univ ≤ 1 := by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ ≤ 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

end BasicProperties

/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：∀ {Ω : Type u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : Measurabl
eSpace Ω'} {ν : MeasureTheory.Measure Ω'}   {κ : ProbabilityTheory.Kernel Ω' Ω} 
{X : Ω → ℝ} {c : NNReal},   (∀ (t : ℝ), MeasureTheory.Integrable (fun ω => Real.
exp (t * X ω)) (ν.bind ⇑κ)) →     (∀ (q : ℚ), ∀ᵐ (ω' : Ω') ∂ν, ProbabilityTheory
.mgf X (κ ω') ↑q ≤ Real.exp (↑c * ↑q ^ 2 / 2)) →       ProbabilityTheory.Kernel.
HasSubgaussianMGF X c κ ν
参数：∀ (t : ℝ), MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) (ν.bind ⇑κ)
；∀ (q : ℚ), ∀ᵐ (ω' : Ω') ∂ν, ProbabilityTheory.mgf X (κ ω') ↑q ≤ Real.exp (↑c * 
↑q ^ 2 / 2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.ae_integrable_of_integrable_comp`：ae_integrable_of
_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) : forallᵐ x ∂μ, Integrable f (κ
 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_le_of_le`：integrable_exp_mul_of_
le_of_le {a b : Real} (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integra
ble (fun ω => exp (b * X ω)) μ) (hat :…
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `DenseRange.induction_on`：DenseRange.induction_on [TopologicalSpace β] {e
 : α -> β} (he : DenseRange e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b
 }) (ih : for…
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `ProbabilityTheory.continuous_mgf`：continuous_mgf (h : forall t, Integrab
le (fun ω => exp (t * X ω)) μ) : Continuous (mgf X μ)
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
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
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
（共 33 条，此处仅展示前 30 条）
-/
protected lemma of_rat (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.HasSubgaussianMGF X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
      have h_int' (n : ℤ) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_int t
      exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)
    filter_upwards [h_mgf, h_int] with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    exact isClosed_le (continuous_mgf h_int) (by fun_prop)

@[simp]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.fun_zero** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 
(fun _ => 0) 0 κ ν where integrable_exp_mul
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureBindCoeKernelOfIsFiniteKernel`：
∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
} {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.mgf_const'`：mgf_const' (c : Real) : mgf (fun _ => c) μ
 t = μ.real Set.univ * exp (t * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure`：∀ {α 
: Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ 
: ProbabilityTheory.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    HasSubgaussianMGF (fun _ ↦ 0) 0 κ ν where
  integrable_exp_mul := by simp
  mgf_le := by simp

@[simp]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.zero** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 
κ ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.fun_zero`：fun_zero [IsFiniteM
easure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF (fun _ => 0) 0 κ ν where 
integrable_exp_mul
-/
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν := fun_zero

@[simp]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.zero_kernel** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：zero_kernel : HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_right`：bind_zero_right (m : Measure α) :
 bind m (0 : α -> Measure β) = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
-/
lemma zero_kernel : HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν := by
  constructor
  · simp [FunLike.coe_zero]
  · simp [exp_nonneg]

@[simp]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.zero_measure** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：zero_measure : HasSubgaussianMGF X c κ (0 : Measure Ω')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_zero_left`：bind_zero_left (f : α -> Measure β
) : bind (0 : Measure α) f = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma zero_measure : HasSubgaussianMGF X c κ (0 : Measure Ω') := ⟨by simp, by simp⟩
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.neg** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：neg {c : Real>=0} (h : HasSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X)
 c κ ν where integrable_exp_mul t
参数：h : HasSubgaussianMGF X c κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma neg {c : ℝ≥0} (h : HasSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X) c κ ν where
  integrable_exp_mul t := by simpa using h.integrable_exp_mul (-t)
  mgf_le := by filter_upwards [h.mgf_le] with ω' hm t using by simpa [mgf] using hm (-t)
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.congr** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：congr {Y : Ω -> Real} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y
) : HasSubgaussianMGF Y c κ ν where integrable_exp_mul t
参数：h : HasSubgaussianMGF X c κ ν；h' : X =ᵐ[κ ∘ₘ ν] Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `MeasureTheory.Measure.ae_ae_of_ae_comp`：ae_ae_of_ae_comp {p : β -> Prop}
 (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω) : forallᵐ ω' ∂μ, forallᵐ ω ∂(κ ω'), p ω
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.mgf_congr`：mgf_congr {Y : Ω -> Real} (h : X =ᵐ[μ] Y) :
 mgf X μ t = mgf Y μ t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma congr {Y : Ω → ℝ} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF Y c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF._root_.ProbabilityTheory.Kernel.Has
SubgaussianMGF_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubg
aussianMGF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr {Y : Ω → ℝ} (h : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF X c κ ν ↔ HasSubgaussianMGF Y c κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY (ae_eq_symm h)⟩
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.of_map** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''} {Y :
 Ω'' -> Ω} {X : Ω -> Real} (hY : Measurable Y) (h : HasSubgaussianMGF X c (κ.map
 Y) ν) : HasSubgaussianMGF (X ∘ Y) c κ ν where integrable_exp_mul t
参数：hY : Measurable Y；h : HasSubgaussianMGF X c (κ.map Y) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.map_comp`：map_comp (μ : Measure α) (κ : Kernel α β
) {f : β -> γ} (hf : Measurable f) : (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul`
：ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, f
orall t, Integrable (fun ω => exp (t * X ω)) (κ ω')
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用引理 `ProbabilityTheory.mgf_map`：mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω
'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) {t : R
eal} (hX : AESt…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
    {Y : Ω'' → Ω} {X : Ω → ℝ} (hY : Measurable Y) (h : HasSubgaussianMGF X c (κ.map Y) ν) :
    HasSubgaussianMGF (X ∘ Y) c κ ν where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t
    convert! h_mgf t
    ext t
    rw [map_apply _ hY, mgf_map hY.aemeasurable]
    convert! (h_int t).1
    rw [map_apply _ hY]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.id_map_iff** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：id_map_iff (hX : Measurable X) : HasSubgaussianMGF id c (κ.map X) ν ↔ HasS
ubgaussianMGF X c κ ν
参数：hX : Measurable X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.of_map`：of_map {Ω'' : Type*} 
{mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''} {Y : Ω'' -> Ω} {X : Ω -> Real} 
(hY : Measurable Y) (h : HasSubgaussian…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.mgf_id_map`：mgf_id_map (hX : AEMeasurable X μ) : mgf i
d (μ.map X) = mgf X μ
（共 31 条，此处仅展示前 30 条）
-/
lemma id_map_iff (hX : Measurable X) :
    HasSubgaussianMGF id c (κ.map X) ν ↔ HasSubgaussianMGF X c κ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ↦ ?_, ?_⟩⟩
  · change HasSubgaussianMGF (id ∘ X) c κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.integrable_exp_mul t
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h.mgf_le
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.const_mul** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：∀ {Ω : Type u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : Measurabl
eSpace Ω'} {ν : MeasureTheory.Measure Ω'}   {κ : ProbabilityTheory.Kernel Ω' Ω} 
{X : Ω → ℝ} {c : NNReal},   ProbabilityTheory.Kernel.HasSubgaussianMGF X c κ ν →
     ∀ (r : ℝ), ProbabilityTheory.Kernel.HasSubgaussianMGF (fun ω => r * X ω) (N
NReal.mk (r ^ 2) ⋯ * c) κ ν
参数：r : ℝ；fun ω => r * X ω；NNReal.mk (r ^ 2) ⋯ * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.mgf_const_mul`：mgf_const_mul (α : Real) : mgf (fun ω =
> α * X ω) μ t = mgf X μ (α * t)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
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
（共 50 条，此处仅展示前 30 条）
-/
protected lemma const_mul (h : HasSubgaussianMGF X c κ ν) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (.mk (r ^ 2) (sq_nonneg r) * c) κ ν where
  integrable_exp_mul t := by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul, mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring

section ChernoffBound

/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_ge_le_exp_add** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：measure_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : Real) : forallᵐ
 ω' ∂ν, forall t, 0 <= t -> (κ ω').real {ω | ε <= X ω} <= exp (-t * ε + c * t ^ 
2 / 2)
参数：h : HasSubgaussianMGF X c κ ν；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.isFiniteMeasure`：isFiniteMeas
ure (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, IsFiniteMeasure (κ ω')
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul`
：ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, f
orall t, Integrable (fun ω => exp (t * X ω)) (κ ω')
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.measure_ge_le_exp_mul_mgf`：measure_ge_le_exp_mul_mgf [
IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t) (h_int : Integrable (fun ω => exp (t
 * X ω)) μ) : μ.real {ω | ε <= X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma measure_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (κ ω').real {ω | ε ≤ X ω} ≤ exp (-t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω').real {ω | ε ≤ X ω}
  _ ≤ exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_ge_le** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：measure_ge_le (h : HasSubgaussianMGF X c κ ν) {ε : Real} (hε : 0 <= ε) : f
orallᵐ ω' ∂ν, (κ ω').real {ω | ε <= X ω} <= exp (-ε ^ 2 / (2 * c))
参数：h : HasSubgaussianMGF X c κ ν；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_univ_le_one`：measure_
univ_le_one (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, κ ω' Set.univ <= 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_ge_le_exp_add`：measur
e_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : Real) : forallᵐ ω' ∂ν, fora
ll t, 0 <= t -> (κ ω').real {ω | ε <= X ω} <= exp (-t …
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
Chernoff bound on the right tail of a sub-Gaussian random variable.
-/
lemma measure_ge_le (h : HasSubgaussianMGF X c κ ν) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc (κ ω').real {ω | ε ≤ X ω}
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (-(ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by congr; field

end ChernoffBound

section Zero

/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_pos_eq_zero_of_hasSubGaussi
anMGF_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF
`。
形式化陈述：measure_pos_eq_zero_of_hasSubGaussianMGF_zero (h : HasSubgaussianMGF X 0 κ
 ν) : forallᵐ ω' ∂ν, (κ ω') {ω | 0 < X ω} = 0
参数：h : HasSubgaussianMGF X 0 κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.cast_pos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linear
Order K] [IsStrictOrderedRing K], 0 < ↑q ↔ 0 < q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.isFiniteMeasure`：isFiniteMeas
ure (h : HasSubgaussianMGF X c κ ν) : forallᵐ ω' ∂ν, IsFiniteMeasure (κ ω')
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_ge_le_exp_add`：measur
e_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : Real) : forallᵐ ω' ∂ν, fora
ll t, 0 <= t -> (κ ω').real {ω | ε <= X ω} <= exp (-t …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_neg_atTop_nhds_zero`：tendsto_exp_neg_atTop_nhds_zero : 
Tendsto (fun x => exp (-x)) atTop (𝓝 0)
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
（共 43 条，此处仅展示前 30 条）
-/
lemma measure_pos_eq_zero_of_hasSubGaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    ∀ᵐ ω' ∂ν, (κ ω') {ω | 0 < X ω} = 0 := by
  have hs : {ω | 0 < X ω} = ⋃ ε : {ε : ℚ // 0 < ε}, {ω | ε ≤ X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hp
      exact ⟨q, (q.cast_pos.1 h1), h2.le⟩
    · intro ⟨q, h1, h2⟩
      exact lt_of_lt_of_le (q.cast_pos.2 h1) h2
  have hb (ε : ℚ) : ∀ᵐ ω' ∂ν, 0 < ε → (κ ω') {ω | ε ≤ X ω} = 0 := by
    filter_upwards [h.measure_ge_le_exp_add ε, h.isFiniteMeasure] with ω' hm _ hε
    simp only [neg_mul, NNReal.coe_zero, zero_mul, zero_div, add_zero] at hm
    suffices (κ ω').real {ω | ε ≤ X ω} = 0 by simpa [Measure.real, ENNReal.toReal_eq_zero_iff]
    have hl : Filter.Tendsto (fun t ↦ rexp (-(t * ε))) Filter.atTop (𝓝 0) := by
      apply tendsto_exp_neg_atTop_nhds_zero.comp
      exact Filter.Tendsto.atTop_mul_const (ε.cast_pos.2 hε) (fun _ a ↦ a)
    apply le_antisymm
    · exact ge_of_tendsto hl (Filter.eventually_atTop.2 ⟨0, hm⟩)
    · exact measureReal_nonneg
  /- `ν`-almost everywhere, `{ω | 0 < X ω}` is a countable union of `κ ω'`-null sets. -/
  filter_upwards [ae_all_iff.2 hb] with ω' hn
  simp only [hs, measure_iUnion_null_iff, Subtype.forall]
  exact fun _ ↦ hn _
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zer
o** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) : for
allᵐ ω' ∂ν, X =ᵐ[κ ω'] 0
参数：h : HasSubgaussianMGF X 0 κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_pos_eq_zero_of_hasSub
GaussianMGF_zero`：measure_pos_eq_zero_of_hasSubGaussianMGF_zero (h : HasSubgauss
ianMGF X 0 κ ν) : forallᵐ ω' ∂ν, (κ ω') {ω | 0 < X ω} = 0
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.neg`：neg {c : Real>=0} (h : H
asSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X) c κ ν where integrable_exp_mu
l t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] 0 := by
  filter_upwards [(h.neg).measure_pos_eq_zero_of_hasSubGaussianMGF_zero,
    h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero]
  intro ω' h1 h2
  simp_rw [Pi.neg_apply, Left.neg_pos_iff] at h1
  apply nonpos_iff_eq_zero.1
  calc (κ ω') {ω | X ω ≠ 0}
  _ = (κ ω') {ω | X ω < 0 ∨ 0 < X ω} := by simp_rw [ne_iff_lt_or_gt]
  _ ≤ (κ ω') {ω | X ω < 0} + (κ ω') {ω | 0 < X ω} := measure_union_le _ _
  _ = 0 := by simp [h1, h2]

/-- Auxiliary lemma for `ae_eq_zero_of_hasSubgaussianMGF_zero'`. -/
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zer
o_of_measurable** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussi
anMGF`。
形式化陈述：ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable (hX : Measurable X) (h 
: HasSubgaussianMGF X 0 κ ν) : X =ᵐ[κ ∘ₘ ν] 0
参数：hX : Measurable X；h : HasSubgaussianMGF X 0 κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用引理 `MeasureTheory.Measure.ae_comp_iff`：ae_comp_iff {p : β -> Prop} (hp : Mea
surableSet {z | p z}) : (forallᵐ z ∂(κ ∘ₘ μ), p z) ↔ forallᵐ y ∂μ, forallᵐ z ∂κ 
y, p z
· 使用定理 `measurableSet_eq_fun`：measurableSet_eq_fun {m : MeasurableSpace α} [Meas
urableSpace β] [MeasurableEq β] {f g : α -> β} (hf : Measurable f) (hg : Measura
ble g) : M…
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
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianM
GF_zero`：ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) : 
forallᵐ ω' ∂ν, X =ᵐ[κ ω'] 0

--- 原说明 ---
Auxiliary lemma for `ae_eq_zero_of_hasSubgaussianMGF_zero'`.
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable
    (hX : Measurable X) (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  rw [Filter.EventuallyEq, Measure.ae_comp_iff (measurableSet_eq_fun hX (by fun_prop))]
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zer
o'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：ae_eq_zero_of_hasSubgaussianMGF_zero' (h : HasSubgaussianMGF X 0 κ ν) : X 
=ᵐ[κ ∘ₘ ν] 0
参数：h : HasSubgaussianMGF X 0 κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.aestronglyMeasurable`：aestron
glyMeasurable (h : HasSubgaussianMGF X c κ ν) : AEStronglyMeasurable X (κ ∘ₘ ν)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.congr`：congr {Y : Ω -> Real} 
(h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) : HasSubgaussianMGF Y c κ 
ν where integrable_exp_mul t
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianM
GF_zero_of_measurable`：ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable (hX : 
Measurable X) (h : HasSubgaussianMGF X 0 κ ν) : X =ᵐ[κ ∘ₘ ν] 0
· 使用定理 `MeasureTheory.AEStronglyMeasurable.measurable_mk`：measurable_mk [PseudoM
etrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf : AEStronglyMeasurable[
m] f μ) : Measurable[m] (hf.mk f)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero' (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  have hX := h.aestronglyMeasurable
  have h' : HasSubgaussianMGF (hX.mk X) 0 κ ν := h.congr hX.ae_eq_mk
  exact hX.ae_eq_mk.trans (ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable hX.measurable_mk h')

end Zero

section Add

/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.add** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：add {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX κ ν) (h
Y : HasSubgaussianMGF Y cY κ ν) : HasSubgaussianMGF (fun ω => X ω + Y ω) ((cX.sq
rt + cY.sqrt) ^ 2) κ ν
参数：hX : HasSubgaussianMGF X cX κ ν；hY : HasSubgaussianMGF Y cY κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.congr`：congr {Y : Ω -> Real} 
(h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) : HasSubgaussianMGF Y c κ 
ν where integrable_exp_mul t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianM
GF_zero'`：ae_eq_zero_of_hasSubgaussianMGF_zero' (h : HasSubgaussianMGF X 0 κ ν) 
: X =ᵐ[κ ∘ₘ ν] 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.memLp_exp_mul`：memLp_exp_mul 
(h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) : MemLp (fun ω => exp (
t * X ω)) p (κ ∘ₘ ν)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_forall_memLp_exp_mul`：ae_f
orall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : Real>=0) : forallᵐ ω' ∂
ν, forall t, MemLp (fun ω => exp (t * X ω)) p (κ ω')
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`：integral_mul_le_Lp_mu
l_Lq_of_nonneg {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real} (hf_no
nneg : 0 <=ᵐ[μ] f) (hg_nonneg : 0 <=ᵐ[μ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
（共 160 条，此处仅展示前 30 条）
-/
lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX κ ν)
    (hY : HasSubgaussianMGF Y cY κ ν) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) κ ν := by
  by_cases hX0 : cX = 0
  · simp only [hX0, NNReal.sqrt_zero, zero_add, NNReal.sq_sqrt] at hX ⊢
    refine hY.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hX] with ω hX0 using by simp [hX0]
  by_cases hY0 : cY = 0
  · simp only [hY0, NNReal.sqrt_zero, add_zero, NNReal.sq_sqrt] at hY ⊢
    refine hX.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hY] with ω hY0 using by simp [hY0]
  exact
  { integrable_exp_mul t := by
      simp_rw [mul_add, exp_add]
      convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
      norm_cast
      infer_instance
    mgf_le := by
      let p := (cX.sqrt + cY.sqrt) / cX.sqrt
      let q := (cX.sqrt + cY.sqrt) / cY.sqrt
      filter_upwards [hX.mgf_le, hY.mgf_le, hX.ae_forall_memLp_exp_mul p,
        hY.ae_forall_memLp_exp_mul q] with ω' hmX hmY hlX hlY t
      calc (κ ω')[fun ω ↦ exp (t * (X ω + Y ω))]
      _ ≤ (κ ω')[fun ω ↦ exp (t * X ω) ^ (p : ℝ)] ^ (1 / (p : ℝ)) *
          (κ ω')[fun ω ↦ exp (t * Y ω) ^ (q : ℝ)] ^ (1 / (q : ℝ)) := by
        simp_rw [mul_add, exp_add]
        apply integral_mul_le_Lp_mul_Lq_of_nonneg
        · exact ⟨by simp [field, p, q], by positivity, by positivity⟩
        · exact ae_of_all _ fun _ ↦ exp_nonneg _
        · exact ae_of_all _ fun _ ↦ exp_nonneg _
        · simpa using (hlX t)
        · simpa using (hlY t)
      _ ≤ exp (cX * (t * p) ^ 2 / 2) ^ (1 / (p : ℝ)) *
          exp (cY * (t * q) ^ 2 / 2) ^ (1 / (q : ℝ)) := by
        simp_rw [← exp_mul _ p, ← exp_mul _ q, mul_right_comm t _ p, mul_right_comm t _ q]
        gcongr
        · exact hmX (t * p)
        · exact hmY (t * q)
      _ = exp ((cX.sqrt + cY.sqrt) ^ 2 * t ^ 2 / 2) := by
        simp_rw [← exp_mul, ← exp_add]
        simp only [NNReal.coe_div, NNReal.coe_add, coe_sqrt, one_div, inv_div, exp_eq_exp, p, q]
        field_simp
        linear_combination t ^ 2 * (-√↑cY * Real.sq_sqrt cX.coe_nonneg
            -√↑cX * Real.sq_sqrt cY.coe_nonneg) }

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {cY : ℝ≥0}
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.prodMkLeft_compProd** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ
 ν)) : HasSubgaussianMGF Y cY (prodMkLeft Ω' η) (ν otimesₘ κ)
参数：h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.prodMkLeft_comp_compProd`：prodMkLeft_comp_compProd
 {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ] : (η.prodMkLeft α) ∘ₘ μ otimes
ₘ κ = η ∘ₘ κ ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
-/
lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF Y cY (prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_add_compProd** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKerne
l η] (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν otimesₘ 
κ)) (t : Real) : Integrable (fun ω => exp (t * (X ω.1 + Y ω.2))) ((κ otimesₖ η) 
∘ₘ ν)
参数：Ω' × Ω；hX : HasSubgaussianMGF X c κ ν；hY : HasSubgaussianMGF Y cY η (ν otimes
ₘ κ)；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_right`：compProd_zero_right (κ : K
ernel α β) (γ : Type*) {mγ : MeasurableSpace γ} : κ otimesₖ (0 : Kernel (α × β) 
γ) = 0
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_right`：bind_zero_right (m : Measure α) :
 bind m (0 : α -> Measure β) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.memLp_exp_mul`：memLp_exp_mul 
(h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) : MemLp (fun ω => exp (
t * X ω)) p (κ ∘ₘ ν)
· 使用引理 `MeasureTheory.Measure.map_comp`：map_comp (μ : Measure α) (κ : Kernel α β
) {f : β -> γ} (hf : Measurable f) : (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd`：fst_compProd (κ : Kernel α β) (η 
: Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] : fst (κ otimesₖ η) =
 κ
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用引理 `MeasureTheory.Measure.comp_compProd_comm`：comp_compProd_comm {η : Kernel
 (α × β) γ} [SFinite μ] [IsSFiniteKernel η] : η ∘ₘ (μ otimesₘ κ) = ((κ otimesₖ η
) ∘ₘ μ).snd
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ENNReal.coe_ofNat`：coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Rea
l>=0) : Real>=0∞) = ofNat(n)
（共 34 条，此处仅展示前 30 条）
-/
lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω.1 + Y ω.2))) ((κ ⊗ₖ η) ∘ₘ ν) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp [FunLike.coe_zero]
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_ofNat] at h
    have : κ ∘ₘ ν = ((κ ⊗ₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst, ← fst_eq, fst_compProd]
    rwa [this, memLp_map_measure_iff h.1 measurable_fst.aemeasurable] at h
  · have h := hY.memLp_exp_mul t 2
    rwa [ENNReal.coe_ofNat, Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff h.1 measurable_snd.aemeasurable] at h

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : (Ω' × Ω) Ω''`, if a random variable `X : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `ν ⊗ₘ κ : Measure (Ω' × Ω)`, then `X + Y` (random
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect to
`κ ⊗ₖ η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.add_compProd** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η] (hX : HasS
ubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν otimesₘ κ)) : HasSubgau
ssianMGF (fun p => X p.1 + Y p.2) (c + cY) (κ otimesₖ η) ν
参数：Ω' × Ω；hX : HasSubgaussianMGF X c κ ν；hY : HasSubgaussianMGF Y cY η (ν otimes
ₘ κ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {ν : MeasureTheo
ry.Measure Ω'}   {κ : ProbabilityTheory…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_add_compProd`：
integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η] (
hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `MeasureTheory.Measure.ae_integrable_of_integrable_comp`：ae_integrable_of
_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) : forallᵐ x ∂μ, Integrable f (κ
 x)
· 使用引理 `MeasureTheory.Measure.ae_ae_of_ae_compProd`：ae_ae_of_ae_compProd [SFinit
e μ] [IsSFiniteKernel κ] {p : α × β -> Prop} (h : forallᵐ x ∂(μ otimesₘ κ), p x)
 : forallᵐ a ∂μ, forallᵐ b ∂κ a,…
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_integrable_exp_mul`：ae_int
egrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) : forallᵐ ω' ∂ν, Inte
grable (fun y => exp (t * X y)) (κ ω')
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `ProbabilityTheory.integral_compProd`：integral_compProd : forall {f : β ×
 γ -> E} (_ : Integrable f ((κ otimesₖ η) a)), ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, 
∫ y, f (x, y) ∂η (a, x) ∂…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
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
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : (Ω' × Ω) Ω''`, if a random vari
able `X : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `
Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `ν ⊗ₘ κ : Measure (Ω' × Ω)`, then `X 
+ Y` (random
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect 
to
`κ ⊗ₖ η : Kernel Ω' (Ω × Ω'')` and `ν`.
-/
lemma add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ η) ν := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_rat (integrable_exp_add_compProd hX hY) fun q ↦ ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul q, Measure.ae_ae_of_ae_compProd hY.mgf_le,
    Measure.ae_integrable_of_integrable_comp <| integrable_exp_add_compProd hX hY q]
    with ω' hX_mgf hX_int hY_mgf h_int_mul
  calc mgf (fun p ↦ X p.1 + Y p.2) ((κ ⊗ₖ η) ω') q
  _ = ∫ x, exp (q * X x) * ∫ y, exp (q * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    simp_rw [mgf, mul_add, exp_add] at h_int_mul ⊢
    simp_rw [integral_compProd h_int_mul, integral_const_mul]
  _ ≤ ∫ x, exp (q * X x) * exp (cY * q ^ 2 / 2) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun ω ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · filter_upwards [all_ae_of hY_mgf q] with ω hY_mgf
      gcongr
      exact hY_mgf
  _ ≤ exp (↑(c + cY) * q ^ 2 / 2) := by
    rw [integral_mul_const, NNReal.coe_add, add_mul, add_div, exp_add]
    gcongr
    exact hX_mgf q

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : Ω Ω''`, if a random variable `X : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `κ ∘ₘ ν : Measure Ω`, then `X + Y` (random
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect to
`κ ⊗ₖ prodMkLeft Ω' η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
/-
**ProbabilityTheory.Kernel.HasSubgaussianMGF.add_comp** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel.HasSubgaussianMGF`。
形式化陈述：add_comp {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η] (hX : HasSubgaussianM
GF X c κ ν) (hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) : HasSubgaussianMGF (fun p 
=> X p.1 + Y p.2) (c + cY) (κ otimesₖ prodMkLeft Ω' η) ν
参数：hX : HasSubgaussianMGF X c κ ν；hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.add_compProd`：add_compProd {η
 : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η] (hX : HasSubgaussianMGF X c κ ν
) (hY : HasSubgaussianMGF Y cY η (ν otimesₘ κ…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.prodMkLeft`：∀ {α : Type u_
1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.prodMkLeft_compProd`：prodMkLe
ft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) : HasSubg
aussianMGF Y cY (prodMkLeft Ω' η) (ν otimesₘ κ)

--- 原说明 ---
For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : Ω Ω''`, if a random variable `X
 : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `
Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `κ ∘ₘ ν : Measure Ω`, then `X + Y` (r
andom
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect 
to
`κ ⊗ₖ prodMkLeft Ω' η : Kernel Ω' (Ω × Ω'')` and `ν`.
-/
lemma add_comp {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end Add

end Kernel.HasSubgaussianMGF

end Kernel

section Conditional

/-! ### Conditionally sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

variable (m) (hm) in
/-- A random variable `X` has a conditionally sub-Gaussian moment-generating function
with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`,
`exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned on `m` is
almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
to the sigma-algebra `m`. -/
/-
**ProbabilityTheory.HasCondSubgaussianMGF** 是 Mathlib 中的一个定义，位于命名空间 `Probability
Theory`。
形式化陈述：HasCondSubgaussianMGF (X : Ω -> Real) (c : Real>=0) (μ : Measure Ω
参数：X : Ω -> Real；c : Real>=0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X` has a conditionally sub-Gaussian moment-generating functio
n
with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for 
all `t : ℝ`,
`exp (t * X)` is `μ`-integrable and the moment-generating function of `X` condit
ioned on `m` is
almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` i
s defined as
sub-Gaussian with respect to the conditional expectation kernel for `m` and the 
restriction of `μ`
to the sigma-algebra `m`.
-/
def HasCondSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubgaussianMGF

/-
**ProbabilityTheory.HasCondSubgaussianMGF.mgf_le** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.HasCondSubgaussianMGF`。
形式化陈述：mgf_le (h : HasCondSubgaussianMGF m hm X c μ) : forallᵐ ω' ∂(μ.trim hm), f
orall t, mgf X (condExpKernel μ m ω') t <= exp (c * t ^ 2 / 2)
参数：h : HasCondSubgaussianMGF m hm X c μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {Ω' 
: Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ} {c :
 NNReal}   {κ : ProbabilityTheory.Kerne…
-/
lemma mgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, mgf X (condExpKernel μ m ω') t ≤ exp (c * t ^ 2 / 2) :=
  Kernel.HasSubgaussianMGF.mgf_le h
/-
**ProbabilityTheory.HasCondSubgaussianMGF.cgf_le** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.HasCondSubgaussianMGF`。
形式化陈述：cgf_le (h : HasCondSubgaussianMGF m hm X c μ) : forallᵐ ω' ∂(μ.trim hm), f
orall t, cgf X (condExpKernel μ m ω') t <= c * t ^ 2 / 2
参数：h : HasCondSubgaussianMGF m hm X c μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.cgf_le`：cgf_le (h : HasSubgau
ssianMGF X c κ ν) : forallᵐ ω' ∂ν, forall t, cgf X (κ ω') t <= c * t ^ 2 / 2
-/
lemma cgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, cgf X (condExpKernel μ m ω') t ≤ c * t ^ 2 / 2 :=
  Kernel.HasSubgaussianMGF.cgf_le h
/-
**ProbabilityTheory.HasCondSubgaussianMGF.ae_trim_condExp_le** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.HasCondSubgaussianMGF`。
形式化陈述：ae_trim_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) : for
allᵐ ω' ∂(μ.trim hm), (μ[fun ω => exp (t * X ω) | m]) ω' <= exp (c * t ^ 2 / 2)
参数：h : HasCondSubgaussianMGF m hm X c μ；t : Real。
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
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel`：condExp_ae_
eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω -> F} [NormedSpace 
Real F] [CompleteSpace F] (hm : m <= mΩ) (hf_int …
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.condExpKernel_comp_trim`：condExpKernel_comp_trim (hm :
 m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.trim.congr_simp`：∀ {α : Type u_1} {m m0 : Measurab
leSpace α} (μ μ_1 : MeasureTheory.Measure α),   μ = μ_1 → ∀ (hm : m ≤ m0), μ.tri
m hm = μ_1.trim hm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.condExpKernel.congr_simp`：∀ {Ω : Type u_3} [mΩ : Measu
rableSpace Ω] [inst : StandardBorelSpace Ω] (μ μ_1 : MeasureTheory.Measure Ω)   
(e_μ : μ = μ_1) [inst_1 : Measur…
· 使用引理 `ProbabilityTheory.HasCondSubgaussianMGF.mgf_le`：mgf_le (h : HasCondSubga
ussianMGF m hm X c μ) : forallᵐ ω' ∂(μ.trim hm), forall t, mgf X (condExpKernel 
μ m ω') t <= exp (c * t ^ 2 / 2)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma ae_trim_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t
/-
**ProbabilityTheory.HasCondSubgaussianMGF.ae_condExp_le** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory.HasCondSubgaussianMGF`。
形式化陈述：ae_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) : forallᵐ 
ω' ∂μ, (μ[fun ω => exp (t * X ω) | m]) ω' <= exp (c * t ^ 2 / 2)
参数：h : HasCondSubgaussianMGF m hm X c μ；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_of_ae_trim`：ae_of_ae_trim (hm : m <= m0) {μ : Measure α
} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.HasCondSubgaussianMGF.ae_trim_condExp_le`：ae_trim_cond
Exp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) : forallᵐ ω' ∂(μ.trim h
m), (μ[fun ω => exp (t * X ω) | m]) ω' <= exp (c…
-/
lemma ae_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) :=
  ae_of_ae_trim hm (h.ae_trim_condExp_le t)

@[simp]
/-
**ProbabilityTheory.HasCondSubgaussianMGF.fun_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.HasCondSubgaussianMGF`。
形式化陈述：fun_zero : HasCondSubgaussianMGF m hm (fun _ => 0) 0 μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.fun_zero`：fun_zero [IsFiniteM
easure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF (fun _ => 0) 0 κ ν where 
integrable_exp_mul
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma fun_zero : HasCondSubgaussianMGF m hm (fun _ ↦ 0) 0 μ := Kernel.HasSubgaussianMGF.fun_zero

@[simp]
/-
**ProbabilityTheory.HasCondSubgaussianMGF.zero** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.HasCondSubgaussianMGF`。
形式化陈述：zero : HasCondSubgaussianMGF m hm 0 0 μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.zero`：zero [IsFiniteMeasure ν
] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma zero : HasCondSubgaussianMGF m hm 0 0 μ := Kernel.HasSubgaussianMGF.zero
/-
**ProbabilityTheory.HasCondSubgaussianMGF.memLp_exp_mul** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory.HasCondSubgaussianMGF`。
形式化陈述：memLp_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) (p : Real>
=0) : MemLp (fun ω => exp (t * X ω)) p μ
参数：h : HasCondSubgaussianMGF m hm X c μ；t : Real；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.memLp_exp_mul`：memLp_exp_mul 
(h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) : MemLp (fun ω => exp (
t * X ω)) p (κ ∘ₘ ν)
· 使用引理 `ProbabilityTheory.condExpKernel_comp_trim`：condExpKernel_comp_trim (hm :
 m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ
-/
lemma memLp_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp_exp_mul h t p
/-
**ProbabilityTheory.HasCondSubgaussianMGF.integrable_exp_mul** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.HasCondSubgaussianMGF`。
形式化陈述：integrable_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) : Int
egrable (fun ω => exp (t * X ω)) μ
参数：h : HasCondSubgaussianMGF m hm X c μ；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Ty
pe u_1} {Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X :
 Ω → ℝ} {c : NNReal}   {κ : ProbabilityTheory.Kerne…
· 使用引理 `ProbabilityTheory.condExpKernel_comp_trim`：condExpKernel_comp_trim (hm :
 m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ
-/
lemma integrable_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

end HasCondSubgaussianMGF

end Conditional

/-! ### Sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A random variable `X` has a sub-Gaussian moment-generating function with parameter `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

This is equivalent to `Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ())`,
as proved in `HasSubgaussianMGF_iff_kernel`.
Properties about sub-Gaussian moment-generating functions should be proved first for
`Kernel.HasSubgaussianMGF` when possible. -/
/-
**ProbabilityTheory.HasSubgaussianMGF** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：HasSubgaussianMGF (X : Ω -> Real) (c : Real>=0) (μ : Measure Ω
参数：X : Ω -> Real；c : Real>=0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X` has a sub-Gaussian moment-generating function with paramet
er `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrabl
e and
the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for al
l `t : ℝ`.
This implies in particular that `X` has expectation 0.

This is equivalent to `Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measu
re.dirac ())`,
as proved in `HasSubgaussianMGF_iff_kernel`.
Properties about sub-Gaussian moment-generating functions should be proved first
 for
`Kernel.HasSubgaussianMGF` when possible.
-/
structure HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)
/-
**ProbabilityTheory.HasSubgaussianMGF_iff_kernel** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：HasSubgaussianMGF_iff_kernel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaus
sianMGF X c (Kernel.const Unit μ) (Measure.dirac ())
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.const_comp`：const_comp {ν : Measure β} : (Kernel.c
onst α ν) ∘ₘ μ = μ Set.univ • ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
-/
lemma HasSubgaussianMGF_iff_kernel :
    HasSubgaussianMGF X c μ
      ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

namespace HasSubgaussianMGF

/-
**ProbabilityTheory.HasSubgaussianMGF.aestronglyMeasurable** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable 
X μ
参数：h : HasSubgaussianMGF X c μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable
/-
**ProbabilityTheory.HasSubgaussianMGF.aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.HasSubgaussianMGF`。
形式化陈述：aemeasurable (h : HasSubgaussianMGF X c μ) : AEMeasurable X μ
参数：h : HasSubgaussianMGF X c μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.aestronglyMeasurable`：aestronglyMeas
urable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ
-/
lemma aemeasurable (h : HasSubgaussianMGF X c μ) : AEMeasurable X μ :=
  h.aestronglyMeasurable.aemeasurable
/-
**ProbabilityTheory.HasSubgaussianMGF.congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.HasSubgaussianMGF`。
形式化陈述：congr (h : HasSubgaussianMGF X c μ) {Y : Ω -> Real} (h' : X =ᵐ[μ] Y) : Has
SubgaussianMGF Y c μ
参数：h : HasSubgaussianMGF X c μ；h' : X =ᵐ[μ] Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.congr`：congr {Y : Ω -> Real} 
(h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) : HasSubgaussianMGF Y c κ 
ν where integrable_exp_mul t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.const_comp`：const_comp {ν : Measure β} : (Kernel.c
onst α ν) ∘ₘ μ = μ Set.univ • ν
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma congr (h : HasSubgaussianMGF X c μ) {Y : Ω → ℝ} (h' : X =ᵐ[μ] Y) :
    HasSubgaussianMGF Y c μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa
/-
**ProbabilityTheory.HasSubgaussianMGF.memLp_exp_mul** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.HasSubgaussianMGF`。
形式化陈述：memLp_exp_mul (h : HasSubgaussianMGF X c μ) (t : Real) (p : Real>=0) : Mem
Lp (fun ω => exp (t * X ω)) p μ
参数：h : HasSubgaussianMGF X c μ；t : Real；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.const_comp`：const_comp {ν : Measure β} : (Kernel.c
onst α ν) ∘ₘ μ = μ Set.univ • ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.memLp_exp_mul`：memLp_exp_mul 
(h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) : MemLp (fun ω => exp (
t * X ω)) p (κ ∘ₘ ν)
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
-/
lemma memLp_exp_mul (h : HasSubgaussianMGF X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul t p
/-
**ProbabilityTheory.HasSubgaussianMGF.cgf_le** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.HasSubgaussianMGF`。
形式化陈述：cgf_le (h : HasSubgaussianMGF X c μ) (t : Real) : cgf X μ t <= c * t ^ 2 /
 2
参数：h : HasSubgaussianMGF X c μ；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `MeasureTheory.all_ae_of`：all_ae_of {ι : Sort*} {p : α -> ι -> Prop} (hp 
: forallᵐ a ∂μ, forall i, p a i) (i : ι) : forallᵐ a ∂μ, p a i
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.cgf_le`：cgf_le (h : HasSubgau
ssianMGF X c κ ν) : forallᵐ ω' ∂ν, forall t, cgf X (κ ω') t <= c * t ^ 2 / 2
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
-/
lemma cgf_le (h : HasSubgaussianMGF X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using (all_ae_of h.cgf_le t)

@[simp]
/-
**ProbabilityTheory.HasSubgaussianMGF.fun_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.HasSubgaussianMGF`。
形式化陈述：fun_zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF (fun _ => 0) 0
 μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.dirac.instIsFiniteMeasure`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {a : α}, MeasureTheory.IsFiniteMeasure (MeasureTheory.Measu
re.dirac a)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…
-/
lemma fun_zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF (fun _ ↦ 0) 0 μ := by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]
/-
**ProbabilityTheory.HasSubgaussianMGF.zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasSubgaussianMGF`。
形式化陈述：zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF 0 0 μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.fun_zero`：fun_zero [IsZeroOrProbabil
ityMeasure μ] : HasSubgaussianMGF (fun _ => 0) 0 μ
-/
lemma zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF 0 0 μ := fun_zero
/-
**ProbabilityTheory.HasSubgaussianMGF.neg** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.HasSubgaussianMGF`。
形式化陈述：neg {c : Real>=0} (h : HasSubgaussianMGF X c μ) : HasSubgaussianMGF (-X) c
 μ
参数：h : HasSubgaussianMGF X c μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.neg`：neg {c : Real>=0} (h : H
asSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X) c κ ν where integrable_exp_mu
l t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
-/
lemma neg {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : HasSubgaussianMGF (-X) c μ := by
  simpa [HasSubgaussianMGF_iff_kernel] using (HasSubgaussianMGF_iff_kernel.1 h).neg
/-
**ProbabilityTheory.HasSubgaussianMGF.of_map** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.HasSubgaussianMGF`。
形式化陈述：of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' ->
 Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)
) : HasSubgaussianMGF (X ∘ Y) c μ where integrable_exp_mul t
参数：hY : AEMeasurable Y μ；h : HasSubgaussianMGF X c (μ.map Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_map`：mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω
'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) {t : R
eal} (hX : AESt…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheory.Measure Ω
) ProbabilityTheory.HasSubgaussi…
-/
lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)) :
    HasSubgaussianMGF (X ∘ Y) c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert! h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]
/-
**ProbabilityTheory.HasSubgaussianMGF.id_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.HasSubgaussianMGF`。
形式化陈述：id_map_iff (hX : AEMeasurable X μ) : HasSubgaussianMGF id c (μ.map X) ↔ Ha
sSubgaussianMGF X c μ
参数：hX : AEMeasurable X μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.of_map`：of_map {Ω' : Type*} {mΩ' : M
easurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasur
able Y μ) (h : HasSubgaussianMGF…
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.mgf_id_map`：mgf_id_map (hX : AEMeasurable X μ) : mgf i
d (μ.map X) = mgf X μ
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheory.Measure Ω
) ProbabilityTheory.HasSubgaussi…
-/
lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubgaussianMGF id c (μ.map X) ↔ HasSubgaussianMGF X c μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ↦ ?_, fun t ↦ ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t
  · rw [mgf_id_map hX]
    exact h.mgf_le t
/-
**ProbabilityTheory.HasSubgaussianMGF.congr_identDistrib** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω
'} {Y : Ω' -> Real} (hX : HasSubgaussianMGF X c μ) (hXY : IdentDistrib X Y μ μ')
 : HasSubgaussianMGF Y c μ'
参数：hX : HasSubgaussianMGF X c μ；hXY : IdentDistrib X Y μ μ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.id_map_iff`：id_map_iff (hX : AEMeasu
rable X μ) : HasSubgaussianMGF id c (μ.map X) ↔ HasSubgaussianMGF X c μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
-/
lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (hX : HasSubgaussianMGF X c μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubgaussianMGF Y c μ' := by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]
/-
**ProbabilityTheory.HasSubgaussianMGF.trim** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasSubgaussianMGF`。
形式化陈述：trim (hm : m <= mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ)
 : HasSubgaussianMGF X c (μ.trim hm) where integrable_exp_mul t
参数：hm : m <= mΩ；hXm : Measurable[m] X；hX : HasSubgaussianMGF X c μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_trim`：integral_trim (hm : m <= m0) {f : β -> G} (
hf : StronglyMeasurable[m] f) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheory.Measure Ω
) ProbabilityTheory.HasSubgaussi…
-/
lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF X c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t
    · exact Measurable.stronglyMeasurable <| by fun_prop
/-
**ProbabilityTheory.HasSubgaussianMGF.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.HasSubgaussianMGF`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X
 : Ω → ℝ} {c : NNReal},   ProbabilityTheory.HasSubgaussianMGF X c μ →     ∀ (r :
 ℝ), ProbabilityTheory.HasSubgaussianMGF (fun ω => r * X ω) (⟨r ^ 2, ⋯⟩ * c) μ
参数：r : ℝ；fun ω => r * X ω；⟨r ^ 2, ⋯⟩ * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
· 使用定理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.const_mul`：∀ {Ω : Type u_1} {
Ω' : Type u_2} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {ν : MeasureT
heory.Measure Ω'}   {κ : ProbabilityTheory…
-/
protected lemma const_mul (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * c) μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r
/-
**ProbabilityTheory.HasSubgaussianMGF.integrableExpSet_eq_univ** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：integrableExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) : integrableExpSet
 X μ = Set.univ
参数：hX : HasSubgaussianMGF X c μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
-/
lemma integrableExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) :
    integrableExpSet X μ = Set.univ := by
  ext t
  simpa using! hX.integrable_exp_mul t
/-
**ProbabilityTheory.HasSubgaussianMGF.memLp** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.HasSubgaussianMGF`。
形式化陈述：memLp (hX : HasSubgaussianMGF X c μ) (p : Real>=0) : MemLp X p μ
参数：hX : HasSubgaussianMGF X c μ；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`：memLp_of_mem_i
nterior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) (p : Real>=0
) : MemLp X p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.integrableExpSet_eq_univ`：integrable
ExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) : integrableExpSet X μ = Set.univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
-/
lemma memLp (hX : HasSubgaussianMGF X c μ) (p : ℝ≥0) : MemLp X p μ :=
  memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX]) p
/-
**ProbabilityTheory.HasSubgaussianMGF.integrable** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.HasSubgaussianMGF`。
形式化陈述：integrable (hX : HasSubgaussianMGF X c μ) : Integrable X μ
参数：hX : HasSubgaussianMGF X c μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrable_of_mem_interior_integrableExpSet`：integrabl
e_of_mem_interior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) : 
Integrable X μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.integrableExpSet_eq_univ`：integrable
ExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) : integrableExpSet X μ = Set.univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
-/
lemma integrable (hX : HasSubgaussianMGF X c μ) : Integrable X μ :=
  integrable_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX])

section ChernoffBound

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.measure_ge_le** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.HasSubgaussianMGF`。
形式化陈述：measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) : μ.r
eal {ω | ε <= X ω} <= exp (-ε ^ 2 / (2 * c))
参数：h : HasSubgaussianMGF X c μ；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.measure_ge_le`：measure_ge_le 
(h : HasSubgaussianMGF X c κ ν) {ε : Real} (hε : 0 <= ε) : forallᵐ ω' ∂ν, (κ ω')
.real {ω | ε <= X ω} <= exp (-ε ^ 2 / (2 * c))
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())

--- 原说明 ---
Chernoff bound on the right tail of a sub-Gaussian random variable.
-/
lemma measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

end ChernoffBound

section Zero

/-
**ProbabilityTheory.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 μ) : X =ᵐ[
μ] 0
参数：h : HasSubgaussianMGF X 0 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianM
GF_zero`：ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) : 
forallᵐ ω' ∂ν, X =ᵐ[κ ω'] 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 μ) : X =ᵐ[μ] 0 := by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).ae_eq_zero_of_hasSubgaussianMGF_zero

end Zero

section Add

/-
**ProbabilityTheory.HasSubgaussianMGF.add** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.HasSubgaussianMGF`。
形式化陈述：add {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ) (hY 
: HasSubgaussianMGF Y cY μ) : HasSubgaussianMGF (fun ω => X ω + Y ω) ((cX.sqrt +
 cY.sqrt) ^ 2) μ
参数：hX : HasSubgaussianMGF X cX μ；hY : HasSubgaussianMGF Y cY μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.add`：add {Y : Ω -> Real} {cX 
cY : Real>=0} (hX : HasSubgaussianMGF X cX κ ν) (hY : HasSubgaussianMGF Y cY κ ν
) : HasSubgaussianMGF (fun ω => X ω …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
-/
lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) μ := by
  have := (HasSubgaussianMGF_iff_kernel.1 hX).add (HasSubgaussianMGF_iff_kernel.1 hY)
  simpa [HasSubgaussianMGF_iff_kernel] using this
/-
**ProbabilityTheory.HasSubgaussianMGF.add_of_indepFun** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：add_of_indepFun {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF 
X cX μ) (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) : HasSubgaussianMGF
 (fun ω => X ω + Y ω) (cX + cY) μ where integrable_exp_mul t
参数：hX : HasSubgaussianMGF X cX μ；hY : HasSubgaussianMGF Y cY μ；hindep : X ⟂ᵢ[μ] 
Y。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.memLp_exp_mul`：memLp_exp_mul (h : Ha
sSubgaussianMGF X c μ) (t : Real) (p : Real>=0) : MemLp (fun ω => exp (t * X ω))
 p μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ProbabilityTheory.IndepFun.mgf_add`：∀ {Ω : Type u_1} {m : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.In
depFun X Y μ →     Measu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheo
ry.Measure Ω) ProbabilityTheory.HasSubgaussi…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.mgf_le`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : Ω → ℝ} {c : NNReal}   {μ : autoParam (MeasureTheory.Measure Ω
) ProbabilityTheory.HasSubgaussi…
· 使用定理 `ProbabilityTheory.mgf_nonneg`：mgf_nonneg : 0 <= mgf X μ t
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 59 条，此处仅展示前 30 条）
-/
lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) (cX + cY) μ where
  integrable_exp_mul t := by
    simp_rw [mul_add, exp_add]
    convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
    norm_cast
    infer_instance
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t).1 (hY.integrable_exp_mul t).1
    _ ≤ exp (cX * t ^ 2 / 2) * exp (cY * t ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX.mgf_le t
      · exact hY.mgf_le t
    _ = exp ((cX + cY) * t ^ 2 / 2) := by rw [← exp_add]; congr; ring
/-
**ProbabilityTheory.HasSubgaussianMGF.sub_of_indepFun** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：sub_of_indepFun {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF 
X cX μ) (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) : HasSubgaussianMGF
 (fun ω => X ω - Y ω) (cX + cY) μ
参数：hX : HasSubgaussianMGF X cX μ；hY : HasSubgaussianMGF Y cY μ；hindep : X ⟂ᵢ[μ] 
Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.add_of_indepFun`：add_of_indepFun {Y 
: Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ) (hY : HasSubgauss
ianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) : Has…
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.neg`：neg {c : Real>=0} (h : HasSubga
ussianMGF X c μ) : HasSubgaussianMGF (-X) c μ
· 使用定理 `ProbabilityTheory.IndepFun.neg_right`：∀ {Ω : Type u_1} {β : Type u_6} {β
' : Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β
}   {g : Ω → β'} {_mβ : Me…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma sub_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω ↦ X ω - Y ω) (cX + cY) μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right
/-
**ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun_of_forall_aemeasurable** 
是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sum_of_iIndepFun_of_forall_aemeasurable
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetSum_of_notMem₀ h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) ?_
    · exact fun i hi ↦ h_subG _ (Finset.mem_insert_of_mem hi)
    · convert! h_indep'
      rw [Finset.sum_apply]
/-
**ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：sum_of_iIndepFun {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ
) {c : ι -> Real>=0} {s : Finset ι} (h_subG : forall i in s, HasSubgaussianMGF (
X i) (c i) μ) : HasSubgaussianMGF (fun ω => ∑ i in s, X i ω) (∑ i in s, c i) μ
参数：h_indep : iIndepFun X μ；h_subG : forall i in s, HasSubgaussianMGF (X i) (c i)
 μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Probability.Moments.SubGaussian.0.ProbabilityTheory.Has
SubgaussianMGF.sum_of_iIndepFun_of_forall_aemeasurable`：∀ {Ω : Type u_1} {mΩ : M
easurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι : Type u_2} {X : ι → Ω → ℝ}, 
  ProbabilityTheory.iIndepFun X μ → …
· 使用定理 `ProbabilityTheory.iIndepFun.precomp`：∀ {Ω : Type u_1} {ι : Type u_2} {x 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → ι} 
  {β : ι → Type u_7} {m :…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.aemeasurable`：aemeasurable (h : HasS
ubgaussianMGF X c μ) : AEMeasurable X μ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.congr`：congr (h : HasSubgaussianMGF 
X c μ) {Y : Ω -> Real} (h' : X =ᵐ[μ] Y) : HasSubgaussianMGF Y c μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
-/
lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ := by
  have : HasSubgaussianMGF (fun ω ↦ ∑ (i : s), X i ω) (∑ (i : s), c i) μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i ↦ (h_subG i i.2).aemeasurable
    · exact fun i _ ↦ h_subG i i.2
  rw [Finset.sum_coe_sort] at this
  exact this.congr (ae_of_all _ fun ω ↦ Finset.sum_attach s (fun i ↦ X i ω))

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι -> Ω -> Real} (h_indep :
 iIndepFun X μ) {c : ι -> Real>=0} {s : Finset ι} (h_subG : forall i in s, HasSu
bgaussianMGF (X i) (c i) μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= ∑ i in s
, X i ω} <= exp (-ε ^ 2 / (2 * ∑ i in s, c i))
参数：h_indep : iIndepFun X μ；h_subG : forall i in s, HasSubgaussianMGF (X i) (c i)
 μ；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`：measure_ge_le (h : Ha
sSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= X ω} <= exp (
-ε ^ 2 / (2 * c))
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun`：sum_of_iIndepFun {
ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ) {c : ι -> Real>=0} {s 
: Finset ι} (h_subG : forall i in s, HasSu…

--- 原说明 ---
**Hoeffding inequality** for sub-Gaussian random variables.
-/
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  (sum_of_iIndepFun h_indep h_subG).measure_ge_le hε

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：measure_sum_range_ge_le_of_iIndepFun {X : Nat -> Ω -> Real} (h_indep : iIn
depFun X μ) {c : Real>=0} {n : Nat} (h_subG : forall i < n, HasSubgaussianMGF (X
 i) c μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= ∑ i in Finset.range n, X i 
ω} <= exp (-ε ^ 2 / (2 * n * c))
参数：h_indep : iIndepFun X μ；h_subG : forall i < n, HasSubgaussianMGF (X i) c μ；hε
 : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`：measure_ge_le (h : Ha
sSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= X ω} <= exp (
-ε ^ 2 / (2 * c))
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun`：sum_of_iIndepFun {
ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ) {c : ι -> Real>=0} {s 
: Finset ι} (h_subG : forall i in s, HasSu…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n

--- 原说明 ---
**Hoeffding inequality** for sub-Gaussian random variables.
-/
lemma measure_sum_range_ge_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    {n : ℕ} (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ exp (-ε ^ 2 / (2 * n * c)) := by
  have h := (sum_of_iIndepFun h_indep (c := fun _ ↦ c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

/-- For `X, Y` two independent sub-Gaussian random variables such that `μ[X] ≥ μ[Y]`,
the probability that `X ≤ Y` is bounded by an exponential decay term. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.measureReal_le_le_exp** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：measureReal_le_le_exp {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussi
anMGF (fun ω => X ω - μ[X]) cX μ) (hY : HasSubgaussianMGF (fun ω => Y ω - μ[Y]) 
cY μ) (hindep : IndepFun X Y μ) (h_le : μ[Y] <= μ[X]) : μ.real {ω | X ω <= Y ω} 
<= Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY)))
参数：hX : HasSubgaussianMGF (fun ω => X ω - μ[X]) cX μ；hY : HasSubgaussianMGF (fun
 ω => Y ω - μ[Y]) cY μ；hindep : IndepFun X Y μ；h_le : μ[Y] <= μ[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`：measure_ge_le (h : Ha
sSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= X ω} <= exp (
-ε ^ 2 / (2 * c))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.sub_of_indepFun`：sub_of_indepFun {Y 
: Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ) (hY : HasSubgauss
ianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) : Has…
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用定理 `ProbabilityTheory.IndepFun.symm`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   {
g : Ω → β'} {x : Meas…
· 使用定理 `Measurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a

--- 原说明 ---
For `X, Y` two independent sub-Gaussian random variables such that `μ[X] ≥ μ[Y]`
,
the probability that `X ≤ Y` is bounded by an exponential decay term.
-/
lemma measureReal_le_le_exp {Y : Ω → ℝ} {cX cY : ℝ≥0}
    (hX : HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) cX μ)
    (hY : HasSubgaussianMGF (fun ω ↦ Y ω - μ[Y]) cY μ)
    (hindep : IndepFun X Y μ) (h_le : μ[Y] ≤ μ[X]) :
    μ.real {ω | X ω ≤ Y ω} ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
  calc μ.real {ω | X ω ≤ Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) ≤ (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω ↦ (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      ?_
    · rw [add_comm cX]
      refine sub_of_indepFun hY hX ?_
      exact hindep.symm.comp (φ := fun x ↦ x - μ[Y]) (ψ := fun x ↦ x - μ[X])
        (by fun_prop) (by fun_prop)
    · grind
    · congr 2
      grind

end Add

end HasSubgaussianMGF

section HoeffdingLemma

/-
**ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X
 : Ω → ℝ}   [MeasureTheory.IsProbabilityMeasure μ] {a b t : ℝ},   AEMeasurable X
 μ →     (∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) →       ∫ (x : Ω), X x ∂μ = 0 → 0 < 
t → ProbabilityTheory.mgf X μ t ≤ Real.exp ((↑‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2)
参数：∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b；x : Ω；(↑‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_mem_Icc`：integrable_exp_mul_of_m
em_Icc [IsFiniteMeasure μ] {X : Ω -> Real} {a b t : Real} (hm : AEMeasurable X μ
) (hb : forallᵐ ω ∂μ, X ω in Set.Icc …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.exists_cgf_eq_iteratedDeriv_two_cgf_mul`：exists_cgf_eq
_iteratedDeriv_two_cgf_mul [IsZeroOrProbabilityMeasure μ] (ht : 0 < t) (hc : μ[X
] = 0) (hs : Set.Icc 0 t subseteq interior (int…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `ProbabilityTheory.variance_tilted_mul`：variance_tilted_mul (ht : t in in
terior (integrableExpSet X μ)) : Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (c
gf X μ) t
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b
· 使用引理 `ProbabilityTheory.variance_le_sq_of_bounded`：variance_le_sq_of_bounded [
IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Real} (h : forallᵐ ω ∂μ, X ω in S
et.Icc a b) (hX : AEMeasurable X …
· 使用引理 `MeasureTheory.isProbabilityMeasure_tilted`：isProbabilityMeasure_tilted [
NeZero μ] (hf : Integrable (fun x => exp (f x)) μ) : IsProbabilityMeasure (μ.til
ted f)
· 使用引理 `MeasureTheory.tilted_absolutelyContinuous`：tilted_absolutelyContinuous (
μ : Measure α) (f : α -> Real) : μ.tilted f ≪ μ
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
（共 67 条，此处仅展示前 30 条）
-/
protected lemma mgf_le_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b t : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X] = 0) (ht : 0 < t) :
    mgf X μ t ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) := by
  have hi (u : ℝ) : Integrable (fun ω ↦ exp (u * X ω)) μ := integrable_exp_mul_of_mem_Icc hm hb
  have hs : Set.Icc 0 t ⊆ interior (integrableExpSet X μ) := by simp [hi, integrableExpSet]
  obtain ⟨u, h1, h2⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hc hs
  rw [← exp_cgf (hi t), exp_le_exp, h2]
  gcongr
  calc
  _ = Var[X; μ.tilted (u * X ·)] := by
    rw [← variance_tilted_mul (hs (Set.mem_Icc_of_Ioo h1))]
  _ ≤ ((b - a) / 2) ^ 2 := by
    convert! variance_le_sq_of_bounded ((tilted_absolutelyContinuous μ (u * X ·)) hb) _
    · exact isProbabilityMeasure_tilted (hi u)
    · exact hm.mono_ac (tilted_absolutelyContinuous μ (u * X ·))
  _ = (‖b - a‖₊ / 2) ^ 2 := by simp [field]

/-- **Hoeffding's lemma**: with respect to a probability measure `μ`, if `X` is a random variable
that has expectation zero and is almost surely in `Set.Icc a b` for some `a ≤ b`, then `X` has a
sub-Gaussian moment-generating function with parameter `((b - a) / 2) ^ 2`. -/
/-
**ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] 
{a b : Real} (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hc
 : μ[X] = 0) : HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ where integrable_exp_m
ul t
参数：hm : AEMeasurable X μ；hb : forallᵐ ω ∂μ, X ω in Set.Icc a b；hc : μ[X] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.integrable_exp_mul_of_mem_Icc`：integrable_exp_mul_of_m
em_Icc [IsFiniteMeasure μ] {X : Ω -> Real} {a b t : Real} (hm : AEMeasurable X μ
) (hb : forallᵐ ω ∂μ, X ω in Set.Icc …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`：∀ {Ω : Type u_1
} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}   [MeasureT
heory.IsProbabilityMeasure μ] {a b t : ℝ},   …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AEMeasurable.neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [inst_1
 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G} {μ
 : Mea…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
**Hoeffding's lemma**: with respect to a probability measure `μ`, if `X` is a ra
ndom variable
that has expectation zero and is almost surely in `Set.Icc a b` for some `a ≤ b`
, then `X` has a
sub-Gaussian moment-generating function with parameter `((b - a) / 2) ^ 2`.
-/
lemma hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X] = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ where
  integrable_exp_mul t := integrable_exp_mul_of_mem_Icc hm hb
  mgf_le t := by
    obtain ht | ht | ht := lt_trichotomy 0 t
    · exact ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
    · simp [← ht]
    calc
    _ = mgf (-X) μ (-t) := by simp [mgf]
    _ ≤ exp ((‖-a - -b‖₊ / 2) ^ 2 * (-t) ^ 2 / 2) := by
      apply ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (hm.neg)
      · filter_upwards [hb] with ω ⟨hl, hr⟩ using ⟨neg_le_neg_iff.2 hr, neg_le_neg_iff.2 hl⟩
      · simp only [Pi.neg_apply]; rw [integral_neg, hc, neg_zero]
      · rwa [Left.neg_pos_iff]
    _ = exp (((‖b - a‖₊ / 2) ^ 2) * t ^ 2 / 2) := by ring_nf

/-- A corollary of Hoeffding's lemma for bounded random variables. -/
/-
**ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : Real} (hm : A
EMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) : HasSubgaussianMGF (fu
n ω => X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ
参数：hm : AEMeasurable X μ；hb : forallᵐ ω ∂μ, X ω in Set.Icc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用引理 `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`：hasS
ubgaussianMGF_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b : Rea
l} (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Se…
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.of_mem_Icc`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) 
  {X : α → ℝ}, AEMeasurab…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A corollary of Hoeffding's lemma for bounded random variables.
-/
lemma hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : ℝ} (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ := by
  rw [← sub_sub_sub_cancel_right b a μ[X]]
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm.sub_const _)
  · filter_upwards [hb] with ω hab using by simpa using hab
  · simp [integral_sub (Integrable.of_mem_Icc a b hm hb) (integrable_const _)]

end HoeffdingLemma

section Martingale

variable [StandardBorelSpace Ω]

/-- If `X` is sub-Gaussian with parameter `cX` with respect to the restriction of `μ` to
a sub-sigma-algebra `m` and `Y` is conditionally sub-Gaussian with parameter `cY` with respect to
`m` and `μ` then `X + Y` is sub-Gaussian with parameter `cX + cY` with respect to `μ`.

`HasSubgaussianMGF X cX (μ.trim hm)` can be obtained from `HasSubgaussianMGF X cX μ` if `X` is
`m`-measurable. See `HasSubgaussianMGF.trim`. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.add_of_hasCondSubgaussianMGF** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：∀ {Ω : Type u_1} {m mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
{X : Ω → ℝ} [inst : StandardBorelSpace Ω]   [inst_1 : MeasureTheory.IsFiniteMeas
ure μ] {Y : Ω → ℝ} {cX cY : NNReal} (hm : m ≤ mΩ),   ProbabilityTheory.HasSubgau
ssianMGF X cX (μ.trim hm) →     ProbabilityTheory.HasCondSubgaussianMGF m hm Y c
Y μ → ProbabilityTheory.HasSubgaussianMGF (X + Y) (cX + cY) μ
参数：hm : m ≤ mΩ；μ.trim hm；X + Y；cX + cY。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF_iff_kernel`：HasSubgaussianMGF_iff_ke
rnel : HasSubgaussianMGF X c μ ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit
 μ) (Measure.dirac ())
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.const_comp`：const_comp {ν : Measure β} : (Kernel.c
onst α ν) ∘ₘ μ = μ Set.univ • ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用引理 `ProbabilityTheory.compProd_trim_condExpKernel`：compProd_trim_condExpKern
el (hm : m <= mΩ) : (μ.trim hm) otimesₘ condExpKernel μ m = @Measure.map Ω (Ω × 
Ω) mΩ (m.prod mΩ) Function.diag μ
· 使用引理 `ProbabilityTheory.Kernel.HasSubgaussianMGF.add_comp`：add_comp {η : Kerne
l Ω Ω''} [IsZeroOrMarkovKernel η] (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubg
aussianMGF Y cY η (κ ∘ₘ ν)) : HasSubgauss…
· 使用定理 `MeasureTheory.instSFiniteOfCountable`：∀ {α : Type u_1} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [Countable α], MeasureTheory.SFinite μ
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.of_map`：of_map {Ω' : Type*} {mΩ' : M
easurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasur
able Y μ) (h : HasSubgaussianMGF…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)

--- 原说明 ---
If `X` is sub-Gaussian with parameter `cX` with respect to the restriction of `μ
` to
a sub-sigma-algebra `m` and `Y` is conditionally sub-Gaussian with parameter `cY
` with respect to
`m` and `μ` then `X + Y` is sub-Gaussian with parameter `cX + cY` with respect t
o `μ`.

`HasSubgaussianMGF X cX (μ.trim hm)` can be obtained from `HasSubgaussianMGF X c
X μ` if `X` is
`m`-measurable. See `HasSubgaussianMGF.trim`.
-/
lemma HasSubgaussianMGF.add_of_hasCondSubgaussianMGF [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {cX cY : ℝ≥0} (hm : m ≤ mΩ)
    (hX : HasSubgaussianMGF X cX (μ.trim hm)) (hY : HasCondSubgaussianMGF m hm Y cY μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ := by
  suffices HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (cX + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ Function.diag := rfl
    rw [h_eq]
    refine HasSubgaussianMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [HasSubgaussianMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubgaussianMGF Y cY (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert! hX.add_comp hY'
  ext
  rw [Kernel.const_apply, ← Measure.compProd, compProd_trim_condExpKernel]

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_add_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.add_of_hasCondSubgaussianMGF

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}

/-- Let `Y` be a random process strongly adapted to a filtration `ℱ`, such that for all `i : ℕ`,
`Y i` is conditionally sub-Gaussian with parameter `cY i` with respect to `ℱ (i - 1)`.
In particular, `n ↦ ∑ i ∈ range n, Y i` is a martingale.
Then the sum `∑ i ∈ range n, Y i` is sub-Gaussian with parameter `∑ i ∈ range n, cY i`. -/
/-
**ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.HasSubgaussianMGF`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [i
nst : StandardBorelSpace Ω] {Y : ℕ → Ω → ℝ}   {cY : ℕ → NNReal} {ℱ : MeasureTheo
ry.Filtration ℕ mΩ} [inst_1 : MeasureTheory.IsZeroOrProbabilityMeasure μ],   Mea
sureTheory.StronglyAdapted ℱ Y →     ProbabilityTheory.HasSubgaussianMGF (Y 0) (
cY 0) μ →       ∀ (n : ℕ),         (∀ i < n - 1, ProbabilityTheory.HasCondSubgau
ssianMGF (↑ℱ i) ⋯ (Y (i + 1)) (cY (i + 1)) μ) →           ProbabilityTheory.HasS
ubgaussianMGF (fun ω => ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i
) μ
参数：Y 0；cY 0；n : ℕ；∀ i < n - 1, ProbabilityTheory.HasCondSubgaussianMGF (↑ℱ i) ⋯ 
(Y (i + 1)) (cY (i + 1)) μ；fun ω => ∑ i ∈ Finset.range n, Y i ω；∑ i ∈ Finset.ran
ge n, cY i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.add_of_hasCondSubgaussianMGF`：∀ {Ω :
 Type u_1} {m mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ} 
[inst : StandardBorelSpace Ω]   [inst_1 : MeasureTheor…
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.trim`：trim (hm : m <= mΩ) (hXm : Mea
surable[m] X) (hX : HasSubgaussianMGF X c μ) : HasSubgaussianMGF X c (μ.trim hm)
 where integrable_exp_mul t
· 使用定理 `Finset.measurable_fun_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u_4
} [inst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {m 
: MeasurableSpa…
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
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…

--- 原说明 ---
Let `Y` be a random process strongly adapted to a filtration `ℱ`, such that for 
all `i : ℕ`,
`Y i` is conditionally sub-Gaussian with parameter `cY i` with respect to `ℱ (i 
- 1)`.
In particular, `n ↦ ∑ i ∈ range n, Y i` is a martingale.
Then the sum `∑ i ∈ range n, Y i` is sub-Gaussian with parameter `∑ i ∈ range n,
 cY i`.
-/
lemma HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi ↦ h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF.add_of_hasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by lia))
      refine HasSubgaussianMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun m hm ↦
        ((h_adapted m).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hm
      lia

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF

/-- **Azuma-Hoeffding inequality** for sub-Gaussian random variables. -/
/-
**ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_sum_ge_le_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ] 
(h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : N
at) (h_subG : forall i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
 (cY (i + 1)) μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= ∑ i in Finset.range
 n, Y i ω} <= exp (-ε ^ 2 / (2 * ∑ i in Finset.range n, cY i))
参数：h_adapted : StronglyAdapted ℱ Y；h0 : HasSubgaussianMGF (Y 0) (cY 0) μ；n : Nat
；h_subG : forall i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY
 (i + 1)) μ；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用引理 `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`：measure_ge_le (h : Ha
sSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) : μ.real {ω | ε <= X ω} <= exp (
-ε ^ 2 / (2 * c))
· 使用定理 `ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`：∀ {Ω :
 Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Standa
rdBorelSpace Ω] {Y : ℕ → Ω → ℝ}   {cY : ℕ → NNReal} {ℱ…

--- 原说明 ---
**Azuma-Hoeffding inequality** for sub-Gaussian random variables.
-/
lemma measure_sum_ge_le_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

@[deprecated (since := "2026-01-27")]
alias measure_sum_ge_le_of_HasCondSubgaussianMGF := measure_sum_ge_le_of_hasCondSubgaussianMGF

end Martingale

end ProbabilityTheory

