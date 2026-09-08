/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic part of the Lindemann-Weierstrass theorem
-/

public section

namespace LindemannWeierstrass

noncomputable section

open scoped Nat
open Complex Polynomial

/-
**LindemannWeierstrass.hasDerivAt_cexp_mul_sumIDeriv** 是 Mathlib 中的一个定理，位于命名空间 `
LindemannWeierstrass`。
形式化陈述：hasDerivAt_cexp_mul_sumIDeriv (p : Complex[X]) (s : Complex) (x : Real) : 
HasDerivAt (fun x : Real => -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s))) (s * 
(cexp (-(x • s)) * p.eval (x • s))) x
参数：p : Complex[X]；s : Complex；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.smul_const`：HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f
 : F) : HasDerivAt (fun y => c y • f) (c' • f) x
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
· 使用定理 `HasDerivAt.cexp`：HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {f' …
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Polynomial.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 (p : Polynomial 𝕜) (x : 𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polyno
mial.eval x…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sumIDeriv_eq_self_add`：sumIDeriv_eq_self_add (p : R[X]) : sum
IDeriv p = p + derivative (sumIDeriv p)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 47 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_cexp_mul_sumIDeriv (p : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring
/-
**LindemannWeierstrass.integral_exp_mul_eval** 是 Mathlib 中的一个定理，位于命名空间 `Lindeman
nWeierstrass`。
形式化陈述：integral_exp_mul_eval (p : Complex[X]) (s : Complex) : s * ∫ x in 0..1, ex
p (-(x • s)) * p.eval (x • s) = -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.e
val 0
参数：p : Complex[X]；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_const_mul`：integral_const_mul [NormedDivisionR
ing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in a..b, r * f x ∂μ 
= r * ∫ x in a..b, f x ∂μ
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt`：integral_eq_sub_of_hasDe
rivAt (hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalInt
egrable f' volume a b) : ∫ y in a..b…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `LindemannWeierstrass.hasDerivAt_cexp_mul_sumIDeriv`：hasDerivAt_cexp_mul_
sumIDeriv (p : Complex[X]) (s : Complex) (x : Real) : HasDerivAt (fun x : Real =
> -(cexp (-(x • s)) * p.sumIDeriv.eval (…
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousOn.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousOn.cexp`：ContinuousOn.cexp (h : ContinuousOn f s) : Continuous
On (fun y => exp (f y)) s
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `ContinuousOn.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 36 条，此处仅展示前 30 条）
-/
theorem integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in 0..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

/--
`P` is a slightly generalized version of `Iᵢ` in
[the wikipedia proof](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstrass_theorem):
`Iᵢ(s) = P(fᵢ, s)`.
-/
/-
**LindemannWeierstrass.P** 是 Mathlib 中的一个定义，位于命名空间 `LindemannWeierstrass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` is a slightly generalized version of `Iᵢ` in
[the wikipedia proof](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstras
s_theorem):
`Iᵢ(s) = P(fᵢ, s)`.
-/
private def P (f : ℂ[X]) (s : ℂ) :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s
/-
**LindemannWeierstrass.P_eq_integral_exp_mul_eval** 是 Mathlib 中的一个定理，位于命名空间 `Lin
demannWeierstrass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem P_eq_integral_exp_mul_eval (f : ℂ[X]) (s : ℂ) :
    P f s = exp s * (s * ∫ x in 0..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [integral_exp_mul_eval, mul_add, mul_neg, exp_neg, mul_inv_cancel_left₀ (exp_ne_zero s),
    neg_add_eq_sub, P]

/--
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
/-
**LindemannWeierstrass.P_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `LindemannWeierstrass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real
 constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a 
nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
private theorem P_le_aux (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p : ℕ,
      ‖P (f p) s‖ ≤
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

/--
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
/-
**LindemannWeierstrass.P_le** 是 Mathlib 中的一个定理，位于命名空间 `LindemannWeierstrass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of complex polynomials `fₚ`, a complex constant `s`, and a real
 constant `c` such
that `|fₚ(xs)| ≤ c ^ p` for all `p ∈ ℕ` and `x ∈ Ioc 0 1`, then there is also a 
nonnegative
constant `c'` such that for all nonzero `p ∈ ℕ`, `|P(fₚ, s)| ≤ c' ^ p`.
-/
private theorem P_le (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p ≠ 0, ‖P (f p) s‖ ≤ c' ^ p := by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : ℝ} : x ≤ max x 1 ^ p :=
    (max_cases x 1).elim (fun h ↦ h.1.symm ▸ le_self_pow₀ h.2 hp)
      fun h ↦ by rw [h.1, one_pow]; exact h.2.le
  gcongr <;> exact le_max_one_pow

/--
Given a polynomial with integer coefficients `p` and a complex constant `s`, there is a nonnegative
`c` such that for all nonzero `q ∈ ℕ`, `|P(X ^ (q - 1) * p ^ q, s)| ≤ c ^ q`.

Note: Jacobson writes `h(x)` for `x ^ (q - 1) * p(x) ^ q` and `bⱼ` for its coefficients.
-/
/-
**LindemannWeierstrass.exp_polynomial_approx_aux** 是 Mathlib 中的一个定理，位于命名空间 `Lind
emannWeierstrass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial with integer coefficients `p` and a complex constant `s`, the
re is a nonnegative
`c` such that for all nonzero `q ∈ ℕ`, `|P(X ^ (q - 1) * p ^ q, s)| ≤ c ^ q`.

Note: Jacobson writes `h(x)` for `x ^ (q - 1) * p(x) ^ q` and `bⱼ` for its coeff
icients.
-/
private theorem exp_polynomial_approx_aux (f : ℤ[X]) (s : ℂ) :
    ∃ c ≥ 0,
      ∀ p ≠ 0, ‖P (map (algebraMap ℤ ℂ) (X ^ (p - 1) * f ^ p)) s‖ ≤ c ^ p := by
  have : Bornology.IsBounded
      ((fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have h :
      (fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 ⊆
        (fun x : ℝ ↦ max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Set.image_mono Set.Ioc_subset_Icc_self
    refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
    fun_prop
  obtain ⟨c, h⟩ := this.exists_norm_le
  simp_rw [Real.norm_eq_abs] at h
  refine P_le _ s c (fun p x hx => ?_)
  specialize h (max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) (Set.mem_image_of_mem _ hx)
  grw [← h]
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, norm_mul,
    Complex.norm_pow, real_smul, norm_mul, norm_real, ← eval₂_eq_eval_map, ← aeval_def, abs_mul,
    abs_norm, mul_pow, Real.norm_of_nonneg hx.1.le]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
  rw [← mul_pow, abs_of_nonneg (by positivity), max_def]
  split_ifs with hx1
  · rw [one_pow]
    exact pow_le_one₀ (mul_nonneg hx.1.le (norm_nonneg _)) hx1
  · push Not at hx1
    exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)

/--
See equation (68), page 285 of [Jacobson, *Basic Algebra I, 4.12*][jacobson1974].

Given a polynomial `f` with integer coefficients, we can find a constant `c : ℝ` and for each prime
`p > |f₀|`, `nₚ : ℤ` and `gₚ : ℤ[X]` such that

* `p` does not divide `nₚ`
* `deg(gₚ) < p * deg(f)`
* all complex roots `r` of `f` satisfy `|nₚ * e ^ r - p * gₚ(r)| ≤ c ^ p / (p - 1)!`

In the proof of Lindemann-Weierstrass, we will take `f` to be a polynomial whose complex roots
are the algebraic numbers whose exponentials we want to prove to be linearly independent.

Note: Jacobson writes `Nₚ` for our `nₚ` and `M` for our `c` (modulo a constant factor).
-/
/-
**LindemannWeierstrass.exp_polynomial_approx** 是 Mathlib 中的一个定理，位于命名空间 `Lindeman
nWeierstrass`。
形式化陈述：exp_polynomial_approx (f : Int[X]) (hf : f.eval 0 != 0) : exists c, forall
 p > (eval 0 f).natAbs, p.Prime -> exists n : Int, ¬ ↑p ∣ n ∧ exists gp : Int[X]
, gp.natDegree <= p * f.natDegree - 1 ∧ forall {r : Complex}, r in f.aroots Comp
lex -> ‖n • exp r - p • aeval r gp‖ <= c ^ p / (p - 1)!
参数：f : Int[X]；hf : f.eval 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Polynomial.eval_sumIDeriv_of_pos`：eval_sumIDeriv_of_pos [CommRing R] [No
ntrivial R] [NoZeroDivisors R] (p : R[X]) {q : Nat} (hq : 0 < q) : exists gp : R
[X], gp.natDegree <= p…
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_pos`：∀ {a : ℤ}, 0 < a.natAbs ↔ a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
· 使用定理 `Int.Prime.dvd_pow'`：Int.Prime.dvd_pow' {n : Int} {k p : Nat} (hp : Nat.P
rime p) (h : (p : Int) ∣ n ^ k) : (p : Int) ∣ n
· 使用定理 `Polynomial.aeval_sumIDeriv`：aeval_sumIDeriv (p : R[X]) (q : Nat) : exist
s gp : R[X], gp.natDegree <= p.natDegree - q ∧ forall (r : A), (X - C r) ^ q ∣ p
.map (algebraMap…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
See equation (68), page 285 of [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
.

Given a polynomial `f` with integer coefficients, we can find a constant `c : ℝ`
 and for each prime
`p > |f₀|`, `nₚ : ℤ` and `gₚ : ℤ[X]` such that

* `p` does not divide `nₚ`
* `deg(gₚ) < p * deg(f)`
* all complex roots `r` of `f` satisfy `|nₚ * e ^ r - p * gₚ(r)| ≤ c ^ p / (p - 
1)!`

In the proof of Lindemann-Weierstrass, we will take `f` to be a polynomial whose
 complex roots
are the algebraic numbers whose exponentials we want to prove to be linearly ind
ependent.

Note: Jacobson writes `Nₚ` for our `nₚ` and `M` for our `c` (modulo a constant f
actor).
-/
theorem exp_polynomial_approx (f : ℤ[X]) (hf : f.eval 0 ≠ 0) :
    ∃ c,
      ∀ p > (eval 0 f).natAbs, p.Prime →
        ∃ n : ℤ, ¬ ↑p ∣ n ∧ ∃ gp : ℤ[X], gp.natDegree ≤ p * f.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ f.aroots ℂ →
            ‖n • exp r - p • aeval r gp‖ ≤ c ^ p / (p - 1)! := by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 Pp'_le using exp_polynomial_approx_aux f
  use
    if h : ((f.aroots ℂ).map c').toFinset.Nonempty then ((f.aroots ℂ).map c').toFinset.max' h else 0
  intro p p_gt prime_p
  obtain ⟨gp', -, h'⟩ := eval_sumIDeriv_of_pos (X ^ (p - 1) * f ^ p) prime_p.pos
  specialize h' 0 (by rw [C_0, sub_zero])
  use f.eval 0 ^ p + p * gp'.eval 0
  constructor
  · rw [dvd_add_left (dvd_mul_right _ _)]
    contrapose! p_gt with h
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hf) (Int.natCast_dvd.mp (Int.Prime.dvd_pow' prime_p h))
  obtain ⟨gp, gp'_le, h⟩ := aeval_sumIDeriv ℂ (X ^ (p - 1) * f ^ p) p
  refine ⟨gp, ?_, ?_⟩
  · refine gp'_le.trans ((tsub_le_tsub_right natDegree_mul_le p).trans ?_)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub prime_p.one_le, tsub_right_comm,
      add_tsub_cancel_left]
  intro r hr
  specialize h r _
  · rw [mem_roots'] at hr
    rw [Polynomial.map_mul, f.map_pow]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) _) _
  rw [nsmul_eq_mul] at h
  have :
      (↑(eval 0 f ^ p + p * eval 0 gp') * cexp r - p * (aeval r) gp) * (p - 1)! =
      ((eval 0 f ^ p * cexp r) * (p - 1)! +
        ↑(p * (p - 1)!) * (eval 0 gp' * cexp r - (aeval r) gp)) := by
    push_cast; ring
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← norm_natCast,
    ← norm_mul, this, Nat.mul_factorial_pred prime_p.ne_zero, mul_sub, ← h]
  have :
      ↑(eval 0 f) ^ p * cexp r * ↑(p - 1)! +
        (↑p ! * (↑(eval 0 gp') * cexp r) - (aeval r) (sumIDeriv (X ^ (p - 1) * f ^ p))) =
      ((p - 1)! • ↑(eval 0 (f ^ p)) + p ! • ↑(eval 0 gp') : ℤ) * cexp r -
        (aeval r) (sumIDeriv (X ^ (p - 1) * f ^ p)) := by
    simp; ring
  rw [this, ← h', mul_comm, ← eq_intCast (algebraMap ℤ ℂ),
    ← aeval_algebraMap_apply_eq_algebraMap_eval, map_zero,
    aeval_sumIDeriv_eq_eval, aeval_sumIDeriv_eq_eval, ← P]
  refine (Pp'_le r p prime_p.ne_zero).trans (pow_le_pow_left₀ (c'0 r) ?_ _)
  have aux : c' r ∈ (Multiset.map c' (f.aroots ℂ)).toFinset := by
    simpa only [Multiset.mem_toFinset] using Multiset.mem_map_of_mem _ hr
  have h : ((f.aroots ℂ).map c').toFinset.Nonempty := ⟨c' r, aux⟩
  simpa only [h, ↓reduceDIte] using Finset.le_max' _ _ aux

end

end LindemannWeierstrass

