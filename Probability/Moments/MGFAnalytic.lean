/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.Taylor

/-!
# The moment-generating function is analytic

The moment-generating function `mgf X μ` of a random variable `X` with respect to a measure `μ`
is analytic on the interior of `integrableExpSet X μ`, the interval on which it is defined.

## Main results

* `analyticOn_mgf`: the moment-generating function is analytic on the interior of the interval
  on which it is defined.
* `iteratedDeriv_mgf`: the n-th derivative of the mgf at `t` is `μ[X ^ n * exp (t * X)]`.

* `analyticOn_cgf`: the cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`.

-/

public section


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ}

/-- For `t : ℝ` with `t ∈ interior (integrableExpSet X μ)`, the derivative of the function
`x ↦ μ[X ^ n * exp (x * X)]` at `t` is `μ[X ^ (n + 1) * exp (t * X)]`. -/
/-
**ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：hasDerivAt_integral_pow_mul_exp_real (ht : t in interior (integrableExpSet
 X μ)) (n : Nat) : HasDerivAt (fun t => μ[fun ω => X ω ^ n * exp (t * X ω)]) μ[f
un ω => X ω ^ (n + 1) * exp (t * X ω)] t
参数：ht : t in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_eq_complex_re`：⇑RCLike.re = Complex.re
· 使用定理 `integral_re`：integral_re {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLik
e.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ)
· 使用引理 `ProbabilityTheory.integrable_pow_mul_cexp_of_re_mem_interior_integrableE
xpSet`：integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hz : z.re in
 interior (integrableExpSet X μ)) (n : Nat) : Integrable (fun ω => …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.hasDerivAt_iff`：Filter.EventuallyEq.hasDerivAt_iff (
h : f₀ =ᶠ[𝓝 x] f₁) : HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x
· 使用定理 `HasDerivAt.real_of_complex`：HasDerivAt.real_of_complex (h : HasDerivAt e
 e' z) : HasDerivAt (fun x : Real => (e x).re) e'.re z
· 使用引理 `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp`：hasDerivAt_integral_p
ow_mul_exp (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) : HasDerivAt
 (fun z => μ[fun ω => X ω ^ n * cexp (z…

--- 原说明 ---
For `t : ℝ` with `t ∈ interior (integrableExpSet X μ)`, the derivative of the fu
nction
`x ↦ μ[X ^ n * exp (x * X)]` at `t` is `μ[X ^ (n + 1) * exp (t * X)]`.
-/
lemma hasDerivAt_integral_pow_mul_exp_real (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun t ↦ μ[fun ω ↦ X ω ^ n * exp (t * X ω)])
      μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] t := by
  have h_re_of_mem n t (ht' : t ∈ interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * exp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re, ← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet ?_ n
      simpa using ht'
  have h_re n : ∀ᶠ t' : ℝ in 𝓝 t, (∫ ω, X ω ^ n * Complex.exp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * exp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _), ← h_re_of_mem _ t ht]
  exact (hasDerivAt_integral_pow_mul_exp (by simp [ht]) n).real_of_complex

section DerivMGF

/-- For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`. -/
/-
**ProbabilityTheory.hasDerivAt_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：hasDerivAt_mgf (h : t in interior (integrableExpSet X μ)) : HasDerivAt (mg
f X μ) (μ[fun ω => X ω * exp (t * X ω)]) t
参数：h : t in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real`：hasDerivAt_integ
ral_pow_mul_exp_real (ht : t in interior (integrableExpSet X μ)) (n : Nat) : Has
DerivAt (fun t => μ[fun ω => X ω ^ n * exp (…

--- 原说明 ---
For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`.
-/
lemma hasDerivAt_mgf (h : t ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (mgf X μ) (μ[fun ω ↦ X ω * exp (t * X ω)]) t := by
  convert! hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp
/-
**ProbabilityTheory.hasDerivAt_iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：hasDerivAt_iteratedDeriv_mgf (ht : t in interior (integrableExpSet X μ)) (
n : Nat) : HasDerivAt (iteratedDeriv n (mgf X μ)) μ[fun ω => X ω ^ (n + 1) * exp
 (t * X ω)] t
参数：ht : t in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ProbabilityTheory.hasDerivAt_mgf`：hasDerivAt_mgf (h : t in interior (int
egrableExpSet X μ)) : HasDerivAt (mgf X μ) (μ[fun ω => X ω * exp (t * X ω)]) t
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.hasDerivAt_iff`：Filter.EventuallyEq.hasDerivAt_iff (
h : f₀ =ᶠ[𝓝 x] f₁) : HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x
· 使用引理 `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real`：hasDerivAt_integ
ral_pow_mul_exp_real (ht : t in interior (integrableExpSet X μ)) (n : Nat) : Has
DerivAt (fun t => μ[fun ω => X ω ^ n * exp (…
-/
lemma hasDerivAt_iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (mgf X μ)) μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] t := by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t ↦ μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 t, y ∈ interior (integrableExpSet X μ) :=
        isOpen_interior.eventually_mem ht
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp_real ht (n + 1)

/-- For `t ∈ interior (integrableExpSet X μ)`, the n-th derivative of `mgf X μ` at `t` is
`μ[X ^ n * exp (t * X)]`. -/
/-
**ProbabilityTheory.iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：iteratedDeriv_mgf (ht : t in interior (integrableExpSet X μ)) (n : Nat) : 
iteratedDeriv n (mgf X μ) t = μ[fun ω => X ω ^ n * exp (t * X ω)]
参数：ht : t in interior (integrableExpSet X μ)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `ProbabilityTheory.hasDerivAt_iteratedDeriv_mgf`：hasDerivAt_iteratedDeriv
_mgf (ht : t in interior (integrableExpSet X μ)) (n : Nat) : HasDerivAt (iterate
dDeriv n (mgf X μ)) μ[fun ω => X ω ^…

--- 原说明 ---
For `t ∈ interior (integrableExpSet X μ)`, the n-th derivative of `mgf X μ` at `
t` is
`μ[X ^ n * exp (t * X)]`.
-/
lemma iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) t = μ[fun ω ↦ X ω ^ n * exp (t * X ω)] := by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

/-- The derivatives of the moment-generating function at zero are the moments. -/
/-
**ProbabilityTheory.iteratedDeriv_mgf_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：iteratedDeriv_mgf_zero (h : 0 in interior (integrableExpSet X μ)) (n : Nat
) : iteratedDeriv n (mgf X μ) 0 = μ[X ^ n]
参数：h : 0 in interior (integrableExpSet X μ)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iteratedDeriv_mgf`：iteratedDeriv_mgf (ht : t in interi
or (integrableExpSet X μ)) (n : Nat) : iteratedDeriv n (mgf X μ) t = μ[fun ω => 
X ω ^ n * exp (t * X ω)]
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The derivatives of the moment-generating function at zero are the moments.
-/
lemma iteratedDeriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) 0 = μ[X ^ n] := by
  simp [iteratedDeriv_mgf h n]

/-- For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`. -/
/-
**ProbabilityTheory.deriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：deriv_mgf (h : t in interior (integrableExpSet X μ)) : deriv (mgf X μ) t =
 μ[fun ω => X ω * exp (t * X ω)]
参数：h : t in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `ProbabilityTheory.hasDerivAt_mgf`：hasDerivAt_mgf (h : t in interior (int
egrableExpSet X μ)) : HasDerivAt (mgf X μ) (μ[fun ω => X ω * exp (t * X ω)]) t

--- 原说明 ---
For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`.
-/
lemma deriv_mgf (h : t ∈ interior (integrableExpSet X μ)) :
    deriv (mgf X μ) t = μ[fun ω ↦ X ω * exp (t * X ω)] :=
  (hasDerivAt_mgf h).deriv
/-
**ProbabilityTheory.deriv_mgf_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：deriv_mgf_zero (h : 0 in interior (integrableExpSet X μ)) : deriv (mgf X μ
) 0 = μ[X]
参数：h : 0 in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.deriv_mgf`：deriv_mgf (h : t in interior (integrableExp
Set X μ)) : deriv (mgf X μ) t = μ[fun ω => X ω * exp (t * X ω)]
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) : deriv (mgf X μ) 0 = μ[X] := by
  simp [deriv_mgf h]

end DerivMGF

section AnalyticMGF

/-- The moment-generating function is analytic at every `t ∈ interior (integrableExpSet X μ)`. -/
/-
**ProbabilityTheory.analyticAt_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：analyticAt_mgf (ht : t in interior (integrableExpSet X μ)) : AnalyticAt Re
al (mgf X μ) t
参数：ht : t in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.re_complexMGF_ofReal'`：re_complexMGF_ofReal' : (fun x 
: Real => (complexMGF X μ x).re) = mgf X μ
· 使用引理 `AnalyticAt.re_ofReal`：AnalyticAt.re_ofReal (hf : AnalyticAt Complex f x)
 : AnalyticAt Real (fun x : Real => (f x).re) x
· 使用引理 `ProbabilityTheory.analyticAt_complexMGF`：analyticAt_complexMGF (hz : z.r
e in interior (integrableExpSet X μ)) : AnalyticAt Complex (complexMGF X μ) z

--- 原说明 ---
The moment-generating function is analytic at every `t ∈ interior (integrableExp
Set X μ)`.
-/
lemma analyticAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℝ (mgf X μ) t := by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal
/-
**ProbabilityTheory.analyticOnNhd_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：analyticOnNhd_mgf : AnalyticOnNhd Real (mgf X μ) (interior (integrableExpS
et X μ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.analyticAt_mgf`：analyticAt_mgf (ht : t in interior (in
tegrableExpSet X μ)) : AnalyticAt Real (mgf X μ) t
-/
lemma analyticOnNhd_mgf : AnalyticOnNhd ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_mgf hx

/-- The moment-generating function is analytic on the interior of the interval on which it is
defined. -/
/-
**ProbabilityTheory.analyticOn_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：analyticOn_mgf : AnalyticOn Real (mgf X μ) (interior (integrableExpSet X μ
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ProbabilityTheory.analyticOnNhd_mgf`：analyticOnNhd_mgf : AnalyticOnNhd R
eal (mgf X μ) (interior (integrableExpSet X μ))

--- 原说明 ---
The moment-generating function is analytic on the interior of the interval on wh
ich it is
defined.
-/
lemma analyticOn_mgf : AnalyticOn ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_mgf.analyticOn
/-
**ProbabilityTheory.hasFPowerSeriesAt_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：hasFPowerSeriesAt_mgf (hv : v in interior (integrableExpSet X μ)) : HasFPo
werSeriesAt (mgf X μ) (FormalMultilinearSeries.ofScalars Real (fun n => (μ[fun ω
 => X ω ^ n * exp (v * X ω)] : Real) / n !)) v
参数：hv : v in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iteratedDeriv_mgf`：iteratedDeriv_mgf (ht : t in interi
or (integrableExpSet X μ)) (n : Nat) : iteratedDeriv n (mgf X μ) t = μ[fun ω => 
X ω ^ n * exp (t * X ω)]
· 使用引理 `AnalyticAt.hasFPowerSeriesAt`：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [
NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (
h : AnalyticAt 𝕜 f…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `ProbabilityTheory.analyticAt_mgf`：analyticAt_mgf (ht : t in interior (in
tegrableExpSet X μ)) : AnalyticAt Real (mgf X μ) t
-/
lemma hasFPowerSeriesAt_mgf (hv : v ∈ interior (integrableExpSet X μ)) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n !)) v := by
  convert! (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]
/-
**ProbabilityTheory.differentiableAt_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：differentiableAt_mgf (ht : t in interior (integrableExpSet X μ)) : Differe
ntiableAt Real (mgf X μ) t
参数：ht : t in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用引理 `ProbabilityTheory.analyticAt_mgf`：analyticAt_mgf (ht : t in interior (in
tegrableExpSet X μ)) : AnalyticAt Real (mgf X μ) t
-/
lemma differentiableAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    DifferentiableAt ℝ (mgf X μ) t := (analyticAt_mgf ht).differentiableAt
/-
**ProbabilityTheory.differentiableOn_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：differentiableOn_mgf : DifferentiableOn Real (mgf X μ) (interior (integrab
leExpSet X μ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `ProbabilityTheory.differentiableAt_mgf`：differentiableAt_mgf (ht : t in 
interior (integrableExpSet X μ)) : DifferentiableAt Real (mgf X μ) t
-/
lemma differentiableOn_mgf : DifferentiableOn ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ (differentiableAt_mgf hx).differentiableWithinAt

-- todo: this should be extended to `integrableExpSet X μ`, not only its interior
/-
**ProbabilityTheory.continuousOn_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：continuousOn_mgf : ContinuousOn (mgf X μ) (interior (integrableExpSet X μ)
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `ProbabilityTheory.differentiableOn_mgf`：differentiableOn_mgf : Different
iableOn Real (mgf X μ) (interior (integrableExpSet X μ))
-/
lemma continuousOn_mgf : ContinuousOn (mgf X μ) (interior (integrableExpSet X μ)) :=
  differentiableOn_mgf.continuousOn
/-
**ProbabilityTheory.continuous_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：continuous_mgf (h : forall t, Integrable (fun ω => exp (t * X ω)) μ) : Con
tinuous (mgf X μ)
参数：h : forall t, Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `interior_eq_univ`：interior_eq_univ : interior s = univ ↔ s = univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `ProbabilityTheory.continuousOn_mgf`：continuousOn_mgf : ContinuousOn (mgf
 X μ) (interior (integrableExpSet X μ))
-/
lemma continuous_mgf (h : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Continuous (mgf X μ) := by
  rw [← continuousOn_univ]
  convert! continuousOn_mgf
  symm
  rw [interior_eq_univ]
  ext t
  simpa using! h t
/-
**ProbabilityTheory.analyticOnNhd_iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：analyticOnNhd_iteratedDeriv_mgf (n : Nat) : AnalyticOnNhd Real (iteratedDe
riv n (mgf X μ)) (interior (integrableExpSet X μ))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `AnalyticOnNhd.iterated_deriv`：AnalyticOnNhd.iterated_deriv [CompleteSpac
e F] (h : AnalyticOnNhd 𝕜 f s) (n : Nat) : AnalyticOnNhd 𝕜 (deriv^[n] f) s
· 使用引理 `ProbabilityTheory.analyticOnNhd_mgf`：analyticOnNhd_mgf : AnalyticOnNhd R
eal (mgf X μ) (interior (integrableExpSet X μ))
-/
lemma analyticOnNhd_iteratedDeriv_mgf (n : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) := by
  rw [iteratedDeriv_eq_iterate]
  exact analyticOnNhd_mgf.iterated_deriv n
/-
**ProbabilityTheory.analyticOn_iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：analyticOn_iteratedDeriv_mgf (n : Nat) : AnalyticOn Real (iteratedDeriv n 
(mgf X μ)) (interior (integrableExpSet X μ))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ProbabilityTheory.analyticOnNhd_iteratedDeriv_mgf`：analyticOnNhd_iterate
dDeriv_mgf (n : Nat) : AnalyticOnNhd Real (iteratedDeriv n (mgf X μ)) (interior 
(integrableExpSet X μ))
-/
lemma analyticOn_iteratedDeriv_mgf (n : ℕ) :
    AnalyticOn ℝ (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) :=
  (analyticOnNhd_iteratedDeriv_mgf n).analyticOn
/-
**ProbabilityTheory.analyticAt_iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：analyticAt_iteratedDeriv_mgf (hv : v in interior (integrableExpSet X μ)) (
n : Nat) : AnalyticAt Real (iteratedDeriv n (mgf X μ)) v
参数：hv : v in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.analyticOnNhd_iteratedDeriv_mgf`：analyticOnNhd_iterate
dDeriv_mgf (n : Nat) : AnalyticOnNhd Real (iteratedDeriv n (mgf X μ)) (interior 
(integrableExpSet X μ))
-/
lemma analyticAt_iteratedDeriv_mgf (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    AnalyticAt ℝ (iteratedDeriv n (mgf X μ)) v :=
  analyticOnNhd_iteratedDeriv_mgf n v hv
/-
**ProbabilityTheory.differentiableAt_iteratedDeriv_mgf** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：differentiableAt_iteratedDeriv_mgf (hv : v in interior (integrableExpSet X
 μ)) (n : Nat) : DifferentiableAt Real (iteratedDeriv n (mgf X μ)) v
参数：hv : v in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用引理 `ProbabilityTheory.analyticAt_iteratedDeriv_mgf`：analyticAt_iteratedDeriv
_mgf (hv : v in interior (integrableExpSet X μ)) (n : Nat) : AnalyticAt Real (it
eratedDeriv n (mgf X μ)) v
-/
lemma differentiableAt_iteratedDeriv_mgf (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    DifferentiableAt ℝ (iteratedDeriv n (mgf X μ)) v :=
  (analyticAt_iteratedDeriv_mgf hv n).differentiableAt

end AnalyticMGF

section AnalyticCGF

/-
**ProbabilityTheory.analyticAt_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：analyticAt_cgf (h : v in interior (integrableExpSet X μ)) : AnalyticAt Rea
l (cgf X μ) v
参数：h : v in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `AnalyticAt.log`：AnalyticAt.log (fa : AnalyticAt Real f x) (m : 0 < f x) 
: AnalyticAt Real (fun z => Real.log (f z)) x
· 使用引理 `ProbabilityTheory.analyticAt_mgf`：analyticAt_mgf (ht : t in interior (in
tegrableExpSet X μ)) : AnalyticAt Real (mgf X μ) t
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
lemma analyticAt_cgf (h : v ∈ interior (integrableExpSet X μ)) : AnalyticAt ℝ (cgf X μ) v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure]
    exact analyticAt_const
  · exact (analyticAt_mgf h).log <| mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)
/-
**ProbabilityTheory.analyticOnNhd_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：analyticOnNhd_cgf : AnalyticOnNhd Real (cgf X μ) (interior (integrableExpS
et X μ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.analyticAt_cgf`：analyticAt_cgf (h : v in interior (int
egrableExpSet X μ)) : AnalyticAt Real (cgf X μ) v
-/
lemma analyticOnNhd_cgf : AnalyticOnNhd ℝ (cgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_cgf hx

/-- The cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`. -/
/-
**ProbabilityTheory.analyticOn_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：analyticOn_cgf : AnalyticOn Real (cgf X μ) (interior (integrableExpSet X μ
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ProbabilityTheory.analyticOnNhd_cgf`：analyticOnNhd_cgf : AnalyticOnNhd R
eal (cgf X μ) (interior (integrableExpSet X μ))

--- 原说明 ---
The cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`.
-/
lemma analyticOn_cgf : AnalyticOn ℝ (cgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_cgf.analyticOn

end AnalyticCGF

section DerivCGF

/-
**ProbabilityTheory.deriv_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：deriv_cgf (h : v in interior (integrableExpSet X μ)) : deriv (cgf X μ) v =
 μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v
参数：h : v in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `deriv.log`：deriv.log (hf : DifferentiableAt Real f x) (hx : f x != 0) : 
deriv (fun x => log (f x)) x = deriv f x / f x
· 使用引理 `ProbabilityTheory.differentiableAt_mgf`：differentiableAt_mgf (ht : t in 
interior (integrableExpSet X μ)) : DifferentiableAt Real (mgf X μ) t
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用引理 `ProbabilityTheory.deriv_mgf`：deriv_mgf (h : t in interior (integrableExp
Set X μ)) : deriv (mgf X μ) t = μ[fun ω => X ω * exp (t * X ω)]
-/
lemma deriv_cgf (h : v ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) v = μ[fun ω ↦ X ω * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure, integral_zero_measure, mgf_zero_measure, div_zero,
      Pi.zero_apply]
    exact deriv_const v 0
  have hv : Integrable (fun ω ↦ exp (v * X ω)) μ := interior_subset (s := integrableExpSet X μ) h
  calc deriv (fun x ↦ log (mgf X μ x)) v
  _ = deriv (mgf X μ) v / mgf X μ v := by
    rw [deriv.log (differentiableAt_mgf h) ((mgf_pos' hμ hv).ne')]
  _ = μ[fun ω ↦ X ω * exp (v * X ω)] / mgf X μ v := by rw [deriv_mgf h]
/-
**ProbabilityTheory.deriv_cgf_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：deriv_cgf_zero (h : 0 in interior (integrableExpSet X μ)) : deriv (cgf X μ
) 0 = μ[X] / μ.real Set.univ
参数：h : 0 in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.deriv_cgf`：deriv_cgf (h : v in interior (integrableExp
Set X μ)) : deriv (cgf X μ) v = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_cgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) 0 = μ[X] / μ.real Set.univ := by simp [deriv_cgf h]
/-
**ProbabilityTheory.iteratedDeriv_two_cgf** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：iteratedDeriv_two_cgf (h : v in interior (integrableExpSet X μ)) : iterate
dDeriv 2 (cgf X μ) v = μ[fun ω => (X ω) ^ 2 * exp (v * X ω)] / mgf X μ v - deriv
 (cgf X μ) v ^ 2
参数：h : v in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `deriv_zero`：deriv_zero : deriv (0 : 𝕜 -> F) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ProbabilityTheory.deriv_cgf`：deriv_cgf (h : v in interior (integrableExp
Set X μ)) : deriv (cgf X μ) v = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v
· 使用引理 `ProbabilityTheory.deriv_mgf`：deriv_mgf (h : t in interior (integrableExp
Set X μ)) : deriv (mgf X μ) t = μ[fun ω => X ω * exp (t * X ω)]
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `deriv_fun_div`：deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) (hx : d x != 0) : deriv (fun x => c x / d x) x = (deriv c x * d
 x …
· 使用定理 `Filter.EventuallyEq.differentiableAt_iff`：Filter.EventuallyEq.differenti
ableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) : DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁
 x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 77 条，此处仅展示前 30 条）
-/
lemma iteratedDeriv_two_cgf (h : v ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω ↦ (X ω) ^ 2 * exp (v * X ω)] / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  by_cases hμ : μ = 0
  · simp [hμ]
  have h_mem : ∀ᶠ y in 𝓝 v, y ∈ interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_d_cgf : deriv (cgf X μ) =ᶠ[𝓝 v] fun u ↦ μ[fun ω ↦ X ω * exp (u * X ω)] / mgf X μ u := by
    filter_upwards [h_mem] with u hu using deriv_cgf hu
  have h_d_mgf : deriv (mgf X μ) =ᶠ[𝓝 v] fun u ↦ μ[fun ω ↦ X ω * exp (u * X ω)] := by
    filter_upwards [h_mem] with u hu using deriv_mgf hu
  rw [h_d_cgf.deriv_eq]
  calc deriv (fun u ↦ (∫ ω, X ω * exp (u * X ω) ∂μ) / mgf X μ u) v
  _ = (deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (mgf X μ) v) / mgf X μ v ^ 2 := by
    rw [deriv_fun_div]
    · rw [h_d_mgf.symm.differentiableAt_iff, ← iteratedDeriv_one]
      exact differentiableAt_iteratedDeriv_mgf h 1
    · exact differentiableAt_mgf h
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * ∫ ω, X ω * exp (v * X ω) ∂μ) / mgf X μ v ^ 2 := by
    rw [deriv_mgf h]
  _ = deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    rw [sub_div]
    congr 1
    · rw [pow_two, div_mul_eq_div_div, mul_div_assoc, div_self, mul_one]
      exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
    · rw [deriv_cgf h]
      ring
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    congr
    convert! (hasDerivAt_integral_pow_mul_exp_real h 1).deriv using 1
    simp
/-
**ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：iteratedDeriv_two_cgf_eq_integral (h : v in interior (integrableExpSet X μ
)) : iteratedDeriv 2 (cgf X μ) v = μ[fun ω => (X ω - deriv (cgf X μ) v) ^ 2 * ex
p (v * X ω)] / mgf X μ v
参数：h : v in interior (integrableExpSet X μ)。
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
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用引理 `iteratedDeriv_const_zero`：iteratedDeriv_const_zero : iteratedDeriv n (0 
: 𝕜 -> F) x = (0 : F)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_zero`：deriv_zero : deriv (0 : 𝕜 -> F) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.iteratedDeriv_two_cgf`：iteratedDeriv_two_cgf (h : v in
 interior (integrableExpSet X μ)) : iteratedDeriv 2 (cgf X μ) v = μ[fun ω => (X 
ω) ^ 2 * exp (v * X ω)] / mgf…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `ProbabilityTheory.deriv_cgf`：deriv_cgf (h : v in interior (integrableExp
Set X μ)) : deriv (cgf X μ) v = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
（共 99 条，此处仅展示前 30 条）
-/
lemma iteratedDeriv_two_cgf_eq_integral (h : v ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω ↦ (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [iteratedDeriv_two_cgf h]
  calc (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ - 2 * (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (cgf X μ) v
      + deriv (cgf X μ) v ^ 2 * mgf X μ v) / mgf X μ v := by
    rw [add_div, sub_div, sub_add]
    congr 1
    rw [mul_div_cancel_right₀, deriv_cgf h]
    · ring
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (∫ ω, ((X ω) ^ 2 - 2 * X ω * deriv (cgf X μ) v + deriv (cgf X μ) v ^ 2) * exp (v * X ω) ∂μ)
      / mgf X μ v := by
    congr 1
    simp_rw [add_mul, sub_mul]
    have h_int : Integrable (fun ω ↦ 2 * X ω * deriv (cgf X μ) v * exp (v * X ω)) μ := by
      simp_rw [mul_assoc, mul_comm (deriv (cgf X μ) v)]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc]
      refine Integrable.mul_const ?_ _
      convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 1
      simp
    rw [integral_add]
    rotate_left
    · exact (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2).sub h_int
    · exact (interior_subset (s := integrableExpSet X μ) h).const_mul _
    rw [integral_sub (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2) h_int]
    congr
    · rw [← integral_const_mul, ← integral_mul_const]
      congr with ω
      ring
    · rw [integral_const_mul, mgf]
  _ = (∫ ω, (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v := by
    congr with ω
    ring
/-
**ProbabilityTheory.exists_cgf_eq_iteratedDeriv_two_cgf_mul** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：exists_cgf_eq_iteratedDeriv_two_cgf_mul [IsZeroOrProbabilityMeasure μ] (ht
 : 0 < t) (hc : μ[X] = 0) (hs : Set.Icc 0 t subseteq interior (integrableExpSet 
X μ)) : exists u in Set.Ioo 0 t, cgf X μ t = (iteratedDeriv 2 (cgf X μ) u) * t ^
 2 / 2
参数：ht : 0 < t；hc : μ[X] = 0；hs : Set.Icc 0 t subseteq interior (integrableExpSet
 X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `Set.uIoo_of_lt`：uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用引理 `ProbabilityTheory.deriv_cgf_zero`：deriv_cgf_zero (h : 0 in interior (int
egrableExpSet X μ)) : deriv (cgf X μ) 0 = μ[X] / μ.real Set.univ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `DifferentiableAt.derivWithin`：DifferentiableAt.derivWithin (h : Differen
tiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = deriv f x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用引理 `ProbabilityTheory.analyticAt_cgf`：analyticAt_cgf (h : v in interior (int
egrableExpSet X μ)) : AnalyticAt Real (cgf X μ) v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.uIcc_of_lt`：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
· 使用定理 `taylorWithinEval_succ`：taylorWithinEval_succ (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ x : Real) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEv
al f n s x₀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `ProbabilityTheory.cgf_zero`：cgf_zero [IsZeroOrProbabilityMeasure μ] : cg
f X μ 0 = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
（共 42 条，此处仅展示前 30 条）
-/
lemma exists_cgf_eq_iteratedDeriv_two_cgf_mul [IsZeroOrProbabilityMeasure μ] (ht : 0 < t)
    (hc : μ[X] = 0) (hs : Set.Icc 0 t ⊆ interior (integrableExpSet X μ)) :
    ∃ u ∈ Set.Ioo 0 t, cgf X μ t = (iteratedDeriv 2 (cgf X μ) u) * t ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (Set.Icc 0 t) := uniqueDiffOn_Icc ht
  rw [← sub_zero (cgf X μ t)]
  nth_rw 3 [← sub_zero t]
  rw [← Set.uIoo_of_lt ht]
  convert! taylor_mean_remainder_lagrange_iteratedDeriv ht.ne ?_
  · have hd : derivWithin (cgf X μ) (Set.Icc 0 t) 0 = 0 := by
      convert! (analyticAt_cgf (hs ⟨le_refl 0, le_of_lt ht⟩)).differentiableAt.derivWithin _
      · simpa [hc] using (deriv_cgf_zero (hs ⟨le_refl 0, le_of_lt ht⟩)).symm
      · exact hu 0 ⟨le_refl 0, le_of_lt ht⟩
    simp [hd, Set.uIcc_of_lt ht]
  · rw [Set.uIcc_of_lt ht]
    exact (analyticOn_cgf.mono hs).contDiffOn hu

end DerivCGF

end ProbabilityTheory

