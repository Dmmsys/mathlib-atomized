/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `CircleIntegrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circleMap c R` is integrable on `[0, 2π]`;

* `circleIntegral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchyPowerSeries f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `hasFPowerSeriesOn_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchyPowerSeries f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `Metric.ball c R`;

* `circleIntegral.integral_sub_zpow_of_undef`, `circleIntegral.integral_sub_zpow_of_ne`, and
  `circleIntegral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circleIntegral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circleIntegral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circleIntegral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see https://github.com/leanprover-community/mathlib4/pull/10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open scoped Real NNReal Interval Pointwise Topology

open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics

/-!
### Facts about `circleMap`
-/

/-- The range of `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
/-
**range_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_circleMap (c : Complex) (R : Real) : range (circleMap c R) = sphere 
c |R|
参数：c : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.range_exp_mul_I`：range_exp_mul_I : (Set.range fun x : Real => ex
p (x * I)) = Metric.sphere 0 1
· 使用定理 `smul_sphere`：smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : Real} (hr :
 0 <= r) : c • sphere x r = sphere (c • x) (‖c‖ * r)
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `vadd_sphere_zero`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ 
: ℝ) (x : E), x +ᵥ Metric.sphere 0 δ = Metric.sphere x δ

--- 原说明 ---
The range of `circleMap c R` is the circle with center `c` and radius `|R|`.
-/
theorem range_circleMap (c : ℂ) (R : ℝ) : range (circleMap c R) = sphere c |R| :=
  calc
    range (circleMap c R) = c +ᵥ R • range fun θ : ℝ => exp (θ * I) := by
      simp +unfoldPartialApp only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I, smul_sphere R 0 zero_le_one]
      simp

/-- The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
/-
**image_circleMap_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_circleMap_Ioc (c : Complex) (R : Real) : circleMap c R '' Ioc 0 (2 *
 π) = sphere c |R|
参数：c : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `range_circleMap`：range_circleMap (c : Complex) (R : Real) : range (circl
eMap c R) = sphere c |R|
· 使用定理 `Function.Periodic.image_Ioc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid 
α] [Archimedean α…
· 使用定理 `periodic_circleMap`：periodic_circleMap (c : Complex) (R : Real) : Period
ic (circleMap c R) (2 * π)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and r
adius `|R|`.
-/
theorem image_circleMap_Ioc (c : ℂ) (R : ℝ) : circleMap c R '' Ioc 0 (2 * π) = sphere c |R| := by
  rw [← range_circleMap, ← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0, zero_add]
/-
**hasDerivAt_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_circleMap (c : Complex) (R : Real) (θ : Real) : HasDerivAt (cir
cleMap c R) (circleMap 0 R θ * I) θ
参数：c : Complex；R : Real；θ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasDerivAt.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `HasDerivAt.cexp`：HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasDerivAt.mul_const`：HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d :
 𝔸) : HasDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `ContinuousLinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {x : 𝕜} (e : 𝕜 →…
-/
theorem hasDerivAt_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : ℂ)).const_add c
/-
**differentiable_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_circleMap (c : Complex) (R : Real) : Differentiable Real (c
ircleMap c R)
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_circleMap`：hasDerivAt_circleMap (c : Complex) (R : Real) (θ :
 Real) : HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ
-/
theorem differentiable_circleMap (c : ℂ) (R : ℝ) : Differentiable ℝ (circleMap c R) := fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt

/-- The circleMap is real analytic. -/
/-
**analyticOnNhd_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_circleMap (c : Complex) (R : Real) : AnalyticOnNhd Real (cir
cleMap c R) Set.univ
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `AnalyticAt.mul`：AnalyticAt.mul {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜
 f z) (hg : AnalyticAt 𝕜 g z) : AnalyticAt 𝕜 (f * g) z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `analyticAt_cexp`：analyticAt_cexp : AnalyticAt Complex exp z
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…

--- 原说明 ---
The circleMap is real analytic.
-/
theorem analyticOnNhd_circleMap (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℝ (circleMap c R) Set.univ := by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

/-- The circleMap is continuously differentiable. -/
/-
**contDiff_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_circleMap (c : Complex) (R : Real) {n : WithTop Nat∞} : ContDiff 
Real n (circleMap c R)
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
· 使用定理 `analyticOnNhd_circleMap`：analyticOnNhd_circleMap (c : Complex) (R : Real
) : AnalyticOnNhd Real (circleMap c R) Set.univ

--- 原说明 ---
The circleMap is continuously differentiable.
-/
theorem contDiff_circleMap (c : ℂ) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (circleMap c R) :=
  (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]
/-
**continuous_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_circleMap (c : Complex) (R : Real) : Continuous (circleMap c R)
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `differentiable_circleMap`：differentiable_circleMap (c : Complex) (R : Re
al) : Differentiable Real (circleMap c R)
-/
theorem continuous_circleMap (c : ℂ) (R : ℝ) : Continuous (circleMap c R) :=
  (differentiable_circleMap c R).continuous

@[fun_prop]
/-
**measurable_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_circleMap (c : Complex) (R : Real) : Measurable (circleMap c R)
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
-/
theorem measurable_circleMap (c : ℂ) (R : ℝ) : Measurable (circleMap c R) :=
  (continuous_circleMap c R).measurable

@[simp]
/-
**deriv_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : deriv (circleMap c R
) θ = circleMap 0 R θ * I
参数：c : Complex；R : Real；θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_circleMap`：hasDerivAt_circleMap (c : Complex) (R : Real) (θ :
 Real) : HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ
-/
theorem deriv_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (hasDerivAt_circleMap _ _ _).deriv
/-
**deriv_circleMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_circleMap_eq_zero_iff {c : Complex} {R : Real} {θ : Real} : deriv (c
ircleMap c R) θ = 0 ↔ R = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem deriv_circleMap_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} :
    deriv (circleMap c R) θ = 0 ↔ R = 0 := by simp [I_ne_zero]
/-
**deriv_circleMap_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_circleMap_ne_zero {c : Complex} {R : Real} {θ : Real} (hR : R != 0) 
: deriv (circleMap c R) θ != 0
参数：hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `deriv_circleMap_eq_zero_iff`：deriv_circleMap_eq_zero_iff {c : Complex} {
R : Real} {θ : Real} : deriv (circleMap c R) θ = 0 ↔ R = 0
-/
theorem deriv_circleMap_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) :
    deriv (circleMap c R) θ ≠ 0 :=
  mt deriv_circleMap_eq_zero_iff.1 hR
/-
**lipschitzWith_circleMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_circleMap (c : Complex) (R : Real) : LipschitzWith (Real.nna
bs R) (circleMap c R)
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_of_nnnorm_deriv_le`：∀ {𝕜 : Type u_3} {G : Type u_4} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup G] [inst_2 : NormedSpace 𝕜 G] {f : 𝕜 → 
G}   {C : NNReal}, Dif…
· 使用定理 `differentiable_circleMap`：differentiable_circleMap (c : Complex) (R : Re
al) : Differentiable Real (circleMap c R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.nnnorm_I`：‖Complex.I‖₊ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
-/
theorem lipschitzWith_circleMap (c : ℂ) (R : ℝ) : LipschitzWith (Real.nnabs R) (circleMap c R) :=
  lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
    NNReal.coe_le_coe.1 <| by simp
/-
**continuous_circleMap_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_circleMap_inv {R : Real} {z w : Complex} (hw : w in ball z R) :
 Continuous fun θ => (circleMap z R θ - w)⁻¹
参数：hw : w in ball z R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `circleMap_ne_mem_ball`：circleMap_ne_mem_ball {c : Complex} {R : Real} {w
 : Complex} (hw : w in ball c R) (θ : Real) : circleMap c R θ != w
· 使用定理 `Continuous.inv₀`：Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x
 != 0) : Continuous f⁻¹
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_circleMap_inv {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R) :
    Continuous fun θ => (circleMap z R θ - w)⁻¹ := by
  have : ∀ θ, circleMap z R θ - w ≠ 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by fun_prop) this
/-
**circleMap_preimage_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleMap_preimage_codiscrete {c : Complex} {R : Real} (hR : R != 0) : map
 (circleMap c R) (codiscrete Real) <= codiscreteWithin (sphere c |R|)
参数：hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.preimage_mem_codiscreteWithin`：AnalyticOnNhd.preimage_mem_
codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜 -> E} (hfU : AnalyticOnNhd 𝕜 f U
) (h₂f : forall x in U, ¬Eventual…
· 使用定理 `analyticOnNhd_circleMap`：analyticOnNhd_circleMap (c : Complex) (R : Real
) : AnalyticOnNhd Real (circleMap c R) Set.univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventuallyConst_iff_exists_eventuallyEq`：eventuallyConst_iff_exis
ts_eventuallyEq [Nonempty β] : EventuallyConst f l ↔ exists c, f =ᶠ[l] fun _ => 
c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Filter.EventuallyEq.deriv`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFiel
d 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {
f f₁ : 𝕜 → F} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `range_circleMap`：range_circleMap (c : Complex) (R : Real) : range (circl
eMap c R) = sphere c |R|
-/
theorem circleMap_preimage_codiscrete {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    map (circleMap c R) (codiscrete ℝ) ≤ codiscreteWithin (sphere c |R|) := by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]
/-
**circleMap_neg_radius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleMap_neg_radius {r x : Real} {c : Complex} : circleMap c (-r) x = cir
cleMap c r (x + π)
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
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Complex.exp_pi_mul_I`：exp_pi_mul_I : exp (π * I) = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem circleMap_neg_radius {r x : ℝ} {c : ℂ} :
    circleMap c (-r) x = circleMap c r (x + π) := by
  simp [circleMap, add_mul, Complex.exp_add]

/-!
### Integrability of a function on a circle
-/

/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circleMap c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circleIntegral` is
`(deriv (circleMap c R) θ) • f (circleMap c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circleMap c R` whenever `R ≠ 0`. -/
@[fun_prop]
/-
**CircleIntegrable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CircleIntegrable (f : Complex -> E) (c : Complex) (R : Real) : Prop
参数：f : Complex -> E；c : Complex；R : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a function `f : ℂ → E` is integrable on the circle with center `c` a
nd radius `R` if
the function `f ∘ circleMap c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circleIntegral` is
`(deriv (circleMap c R) θ) • f (circleMap c R θ)`. Integrability of this functio
n is equivalent
to integrability of `f ∘ circleMap c R` whenever `R ≠ 0`.
-/
def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
  IntervalIntegrable (fun θ : ℝ ↦ f (circleMap c R θ)) volume 0 (2 * π)
/-
**circleIntegrable_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_def (f : Complex -> E) (c : Complex) (R : Real) : CircleI
ntegrable f c R ↔ IntervalIntegrable (fun θ : Real => f (circleMap c R θ)) volum
e 0 (2 * π)
参数：f : Complex -> E；c : Complex；R : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem circleIntegrable_def (f : ℂ → E) (c : ℂ) (R : ℝ) : CircleIntegrable f c R ↔
    IntervalIntegrable (fun θ : ℝ ↦ f (circleMap c R θ)) volume 0 (2 * π) := Iff.rfl

@[simp, fun_prop]
/-
**circleIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_const (a : E) (c : Complex) (R : Real) : CircleIntegrable
 (fun _ => a) c R
参数：a : E；c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
-/
theorem circleIntegrable_const (a : E) (c : ℂ) (R : ℝ) : CircleIntegrable (fun _ => a) c R :=
  intervalIntegrable_const

@[fun_prop]
/-
**circleIntegrable_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_id (c : Complex) (R : Real) : CircleIntegrable (fun z => 
z) c R
参数：c : Complex；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
-/
theorem circleIntegrable_id (c : ℂ) (R : ℝ) : CircleIntegrable (fun z => z) c R :=
  (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

namespace CircleIntegrable

variable {f g : ℂ → E} {c : ℂ} {R : ℝ} {A : Type*} [NormedRing A] {a : A}

/--
Analogue of `IntervalIntegrable.abs`: If a real-valued function `f` is circle integrable, then so is
`|f|`.
-/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.abs** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：abs {f : Complex -> Real} (hf : CircleIntegrable f c R) : CircleIntegrable
 |f| c R
参数：hf : CircleIntegrable f c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.abs`：abs {f : Real -> Real} (h : IntervalIntegrable f
 μ a b) : IntervalIntegrable (fun x => |f x|) μ a b

--- 原说明 ---
Analogue of `IntervalIntegrable.abs`: If a real-valued function `f` is circle in
tegrable, then so is
`|f|`.
-/
theorem abs {f : ℂ → ℝ} (hf : CircleIntegrable f c R) :
    CircleIntegrable |f| c R := IntervalIntegrable.abs hf

@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.add** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) : CircleIn
tegrable (f + g) c R
参数：hf : CircleIntegrable f c R；hg : CircleIntegrable g c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f + g) c R :=
  IntervalIntegrable.add hf hg

@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：sub (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) : CircleIn
tegrable (f - g) c R
参数：hf : CircleIntegrable f c R；hg : CircleIntegrable g c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.sub`：sub {f g : Real -> E} (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x - g
 x) μ a b
-/
theorem sub (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f - g) c R :=
  IntervalIntegrable.sub hf hg

/-- Sums of circle integrable functions are circle integrable. -/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.sum** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c : ℂ} {R : ℝ} {ι : Type u
_3} (s : Finset ι) {f : ι → ℂ → E},   (∀ i ∈ s, CircleIntegrable (f i) c R) → Ci
rcleIntegrable (∑ i ∈ s, f i) c R
参数：s : Finset ι；∀ i ∈ s, CircleIntegrable (f i) c R；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CircleIntegrable.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (f
 : ℂ → E) (c : ℂ) (R : ℝ),   CircleIntegrable f c R = IntervalIntegrable (fun θ 
=> f (circl…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntervalIntegrable.sum`：sum {ε} [TopologicalSpace ε] [ENormedAddCommMono
id ε] [ContinuousAdd ε] (s : Finset ι) {f : ι -> Real -> ε} (h : forall i in s, 
IntervalInte…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Sums of circle integrable functions are circle integrable.
-/
protected theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ i ∈ s, f i) c R := by
  rw [CircleIntegrable, (by aesop : (fun θ ↦ (∑ i ∈ s, f i) (circleMap c R θ))
    = ∑ i ∈ s, fun θ ↦ f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h

/-- `finsum`s of circle integrable functions are circle integrable. -/
@[fun_prop]
/-
**CircleIntegrable.finsum** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c : ℂ} {R : ℝ} {ι : Type u
_3} {f : ι → ℂ → E},   (∀ (i : ι), CircleIntegrable (f i) c R) → CircleIntegrabl
e (∑ᶠ (i : ι), f i) c R
参数：∀ (i : ι), CircleIntegrable (f i) c R；∑ᶠ (i : ι), f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `CircleIntegrable.sum`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c 
: ℂ} {R : ℝ} {ι : Type u_3} (s : Finset ι) {f : ι → ℂ → E},   (∀ i ∈ s, CircleIn
tegrable (…
· 使用定理 `finsum_of_infinite_support`：∀ {α : Type u_1} {M : Type u_5} [inst : AddC
ommMonoid M] {f : α → M},   (Function.support f).Infinite → ∑ᶠ (i : α), f i = 0
· 使用定理 `circleIntegrable_const`：circleIntegrable_const (a : E) (c : Complex) (R 
: Real) : CircleIntegrable (fun _ => a) c R

--- 原说明 ---
`finsum`s of circle integrable functions are circle integrable.
-/
protected theorem finsum {ι : Type*} {f : ι → ℂ → E} (h : ∀ i, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ᶠ i, f i) c R := by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ ↦ h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

@[to_fun (attr := fun_prop)]
nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg

/-- If `f` is circle integrable, then so are its scalar multiples. -/
@[to_fun (attr := fun_prop) const_fun_smul]
/-
**CircleIntegrable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：const_smul {f : Complex -> A} (h : CircleIntegrable f c R) : CircleIntegra
ble (a • f) c R
参数：h : CircleIntegrable f c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b

--- 原说明 ---
If `f` is circle integrable, then so are its scalar multiples.
-/
theorem const_smul {f : ℂ → A} (h : CircleIntegrable f c R) : CircleIntegrable (a • f) c R :=
  IntervalIntegrable.const_mul h _

variable
  {𝕜 F : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g • f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.continuousOn_smul** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable
`。
形式化陈述：continuousOn_smul {f : Complex -> F} {g : Complex -> 𝕜} (hf : CircleIntegr
able f c R) (hg : ContinuousOn g (sphere c |R|)) : CircleIntegrable (g • f) c R
参数：hf : CircleIntegrable f c R；hg : ContinuousOn g (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.continuousOn_smul`：continuousOn_smul (hg : IntervalIn
tegrable g μ a b) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, 
then `g • f` is
circle integrable.
-/
theorem continuousOn_smul {f : ℂ → F} {g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g • f) c R :=
  IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f • g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.smul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable
`。
形式化陈述：smul_continuousOn {f : Complex -> 𝕜} {g : Complex -> F} (hf : CircleIntegr
able f c R) (hg : ContinuousOn g (sphere c |R|)) : CircleIntegrable (f • g) c R
参数：hf : CircleIntegrable f c R；hg : ContinuousOn g (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.smul_continuousOn`：smul_continuousOn (hf : IntervalIn
tegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => 
f x • g x) μ a b
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, 
then `f • g` is
circle integrable.
-/
theorem smul_continuousOn {f : ℂ → 𝕜} {g : ℂ → F} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f • g) c R :=
  IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g * f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.continuousOn_mul** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`
。
形式化陈述：continuousOn_mul {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R) (hg : 
ContinuousOn g (sphere c |R|)) : CircleIntegrable (g * f) c R
参数：hf : CircleIntegrable f c R；hg : ContinuousOn g (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, 
then `g * f` is
circle integrable.
-/
theorem continuousOn_mul {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g * f) c R :=
  IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f * g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/-
**CircleIntegrable.mul_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`
。
形式化陈述：mul_continuousOn {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R) (hg : 
ContinuousOn g (sphere c |R|)) : CircleIntegrable (f * g) c R
参数：hf : CircleIntegrable f c R；hg : ContinuousOn g (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mul_continuousOn`：mul_continuousOn {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => f x * g x…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, 
then `f * g` is
circle integrable.
-/
theorem mul_continuousOn {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f * g) c R :=
  IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

@[deprecated (since := "2026-07-01")] alias smul_of_continuousOn := continuousOn_smul
@[deprecated (since := "2026-07-01")] alias mul_of_continuousOn := continuousOn_mul
@[deprecated (since := "2026-07-01")] alias fun_smul_of_continuousOn := fun_continuousOn_smul
@[deprecated (since := "2026-07-01")] alias fun_mul_of_continuousOn := fun_continuousOn_mul

/-- The function we actually integrate over `[0, 2π]` in the definition of `circleIntegral` is
integrable. -/
/-
**CircleIntegrable.out** 是 Mathlib 中的一个定理，位于命名空间 `CircleIntegrable`。
形式化陈述：out [NormedSpace Complex E] (hf : CircleIntegrable f c R) : IntervalIntegr
able (fun θ : Real => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2
 * π)
参数：hf : CircleIntegrable f c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The function we actually integrate over `[0, 2π]` in the definition of `circleIn
tegral` is
integrable.
-/
theorem out [NormedSpace ℂ E] (hf : CircleIntegrable f c R) :
    IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0
      (2 * π) := by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]

end CircleIntegrable

@[simp]
/-
**circleIntegrable_zero_radius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_zero_radius {f : Complex -> E} {c : Complex} : CircleInte
grable f c 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `circleMap_zero_radius`：circleMap_zero_radius (c : Complex) : circleMap c
 0 = const Real c
-/
theorem circleIntegrable_zero_radius {f : ℂ → E} {c : ℂ} : CircleIntegrable f c 0 := by
  simp [CircleIntegrable]

/--
Circle integrability depends only on the restriction of the function to the sphere.
-/
/-
**circleIntegrable_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_congr {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf
 : Set.EqOn f₁ f₂ (sphere c |R|)) : CircleIntegrable f₁ c R ↔ CircleIntegrable f
₂ c R
参数：hf : Set.EqOn f₁ f₂ (sphere c |R|)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegrable_congr`：intervalIntegrable_congr {g : Real -> ε} (h : 
EqOn f g (Ι a b)) : IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|

--- 原说明 ---
Circle integrability depends only on the restriction of the function to the sphe
re.
-/
theorem circleIntegrable_congr {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  intervalIntegrable_congr fun x _ ↦ hf (circleMap_mem_sphere' c R x)

@[deprecated (since := "2026-04-26")] alias crcleIntegrable_congr := circleIntegrable_congr

/--
Circle integrability is invariant when taking negative radius.
-/
/-
**circleIntegrable_neg_radius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c : ℂ} {R : ℝ} {f : ℂ → E}
,   CircleIntegrable f c (-R) ↔ CircleIntegrable f c R
参数：-R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_congr`：intervalIntegrable_congr {g : Real -> ε} (h : 
EqOn f g (Ι a b)) : IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `circleMap_neg_radius`：circleMap_neg_radius {r x : Real} {c : Complex} : 
circleMap c (-r) x = circleMap c r (x + π)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntervalIntegrable.comp_add_right_iff`：comp_add_right_iff {c : Real} (h 
: ‖f (min a b + c)‖ₑ != ⊤
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.Periodic.intervalIntegrable_iff`：intervalIntegrable_iff {t₁ t₂ 
: Real} (hf : Periodic f T) : IntervalIntegrable f volume t₁ (t₁ + T) ↔ Interval
Integrable f volume t₂ (t₂ + T…
· 使用定理 `Function.Periodic.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
f : α → β} {c : α} [inst : Add α],   Function.Periodic f c → ∀ (g : β → γ), Func
tion.Periodi…
· 使用定理 `periodic_circleMap`：periodic_circleMap (c : Complex) (R : Real) : Period
ic (circleMap c R) (2 * π)

--- 原说明 ---
Circle integrability is invariant when taking negative radius.
-/
@[simp] theorem circleIntegrable_neg_radius {c : ℂ} {R : ℝ} {f : ℂ → E} :
    CircleIntegrable f c (-R) ↔ CircleIntegrable f c R := by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ ↦ f (circleMap c (-R) θ))
    (g := fun θ ↦ (f ∘ (circleMap c R)) (θ + π)) (fun _ _ ↦ by simp [circleMap_neg_radius]),
    IntervalIntegrable.comp_add_right_iff (c := π), add_comm (2 * π) π]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₂ := 0)

/-- Circle integrability is invariant when functions change along discrete sets. -/
/-
**CircleIntegrable.congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CircleIntegrable.congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : 
Complex -> E} (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hf₁ : CircleInte
grable f₁ c R) : CircleIntegrable f₂ c R
参数：hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂；hf₁ : CircleIntegrable f₁ c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_congr_codiscreteWithin`：intervalIntegrable_congr_codi
screteWithin {g : Real -> ε} [NullSingletonClass μ] (h : f =ᶠ[codiscreteWithin (
Ι a b)] g) : IntervalIntegrable…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `circleMap_preimage_codiscrete`：circleMap_preimage_codiscrete {c : Comple
x} {R : Real} (hR : R != 0) : map (circleMap c R) (codiscrete Real) <= codiscret
eWithin (sphere c |…

--- 原说明 ---
Circle integrability is invariant when functions change along discrete sets.
-/
theorem CircleIntegrable.congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hf₁ : CircleIntegrable f₁ c R) :
    CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

/-- Circle integrability is invariant when functions change along discrete sets. -/
/-
**circleIntegrable_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : 
Complex -> E} (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) : CircleIntegrabl
e f₁ c R ↔ CircleIntegrable f₂ c R
参数：hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleIntegrable.congr_codiscreteWithin`：CircleIntegrable.congr_codiscre
teWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf : f₁ =ᶠ[codiscreteW
ithin (sphere c |R|)] f₂) (hf…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
Circle integrability is invariant when functions change along discrete sets.
-/
theorem circleIntegrable_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  ⟨(CircleIntegrable.congr_codiscreteWithin hf ·),
    (CircleIntegrable.congr_codiscreteWithin hf.symm ·)⟩
/-
**circleIntegrable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_iff [NormedSpace Complex E] {f : Complex -> E} {c : Compl
ex} (R : Real) : CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : Real => de
riv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π)
参数：R : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `circleMap_zero_radius`：circleMap_zero_radius (c : Complex) : circleMap c
 0 = const Real c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `CircleIntegrable.out`：out [NormedSpace Complex E] (hf : CircleIntegrable
 f c R) : IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circl
eMap c R θ…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
（共 57 条，此处仅展示前 30 条）
-/
theorem circleIntegrable_iff [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} (R : ℝ) :
    CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) := by
  by_cases h₀ : R = 0
  · simp +unfoldPartialApp [h₀, const]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H : ∀ {θ}, circleMap 0 R θ * I ≠ 0 := fun {θ} => by simp [h₀, I_ne_zero]
    simpa only [inv_smul_smul₀ H]
      using ((continuous_circleMap 0 R).aestronglyMeasurable.mul_const
        I).aemeasurable.fun_inv.aestronglyMeasurable.fun_smul h.aestronglyMeasurable
  · simp [norm_smul, h₀]

@[fun_prop]
/-
**ContinuousOn.circleIntegrable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.circleIntegrable' {f : Complex -> E} {c : Complex} {R : Real}
 (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R
参数：hf : ContinuousOn f (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
-/
theorem ContinuousOn.circleIntegrable' {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R :=
  (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _
/-
**ContinuousOn.circleIntegrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.circleIntegrable {f : Complex -> E} {c : Complex} {R : Real} 
(hR : 0 <= R) (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R
参数：hR : 0 <= R；hf : ContinuousOn f (sphere c R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.circleIntegrable'`：ContinuousOn.circleIntegrable' {f : Comp
lex -> E} {c : Complex} {R : Real} (hf : ContinuousOn f (sphere c |R|)) : Circle
Integrable f c R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem ContinuousOn.circleIntegrable {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R :=
  ContinuousOn.circleIntegrable' <| (abs_of_nonneg hR).symm ▸ hf

/-- The function `fun z ↦ (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c`
and radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp]
/-
**circleIntegrable_sub_zpow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_sub_zpow_iff {c w : Complex} {R : Real} {n : Int} : Circl
eIntegrable (fun z => (z - w) ^ n) c R ↔ R = 0 ∨ 0 <= n ∨ w ∉ sphere c |R|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `circleIntegrable_iff`：circleIntegrable_iff [NormedSpace Complex E] {f : 
Complex -> E} {c : Complex} (R : Real) : CircleIntegrable f c R ↔ IntervalIntegr
able (fun …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `image_circleMap_Ioc`：image_circleMap_Ioc (c : Complex) (R : Real) : circ
leMap c R '' Ioc 0 (2 * π) = sphere c |R|
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `not_intervalIntegrable_of_sub_inv_isBigO_punctured`：not_intervalIntegrab
le_of_sub_inv_isBigO_punctured {f : Real -> F} {a b c : Real} (hf : (fun x => (x
 - c)⁻¹) =O[𝓝[!=] c] f) (hne : a != b) (…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
The function `fun z ↦ (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle 
with center `c`
and radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to th
is circle.
-/
theorem circleIntegrable_sub_zpow_iff {c w : ℂ} {R : ℝ} {n : ℤ} :
    CircleIntegrable (fun z => (z - w) ^ n) c R ↔ R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c |R| := by
  constructor
  · intro h; contrapose! h; rcases h with ⟨hR, hn, hw⟩
    simp only [circleIntegrable_iff R, deriv_circleMap]
    rw [← image_circleMap_Ioc] at hw; rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ ∈ [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ
    set f : ℝ → ℂ := fun θ' => circleMap c R θ' - circleMap c R θ
    have : ∀ᶠ θ' in 𝓝[≠] θ, f θ' ∈ ball (0 : ℂ) 1 \ {0} := by
      suffices ∀ᶠ z in 𝓝[≠] circleMap c R θ, z - circleMap c R θ ∈ ball (0 : ℂ) 1 \ {0} from
        ((differentiable_circleMap c R θ).hasDerivAt.tendsto_nhdsNE
          (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    refine (((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).inv_rev
      (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans ?_
    refine IsBigO.of_bound |R|⁻¹ (this.mono fun θ' hθ' => ?_)
    set x := ‖f θ'‖
    suffices x⁻¹ ≤ x ^ n by
      simp only [smul_eq_mul, norm_mul,
        norm_inv, norm_I, mul_one]
      simpa only [norm_circleMap_zero, norm_zpow, Ne, abs_eq_zero.not.2 hR, not_false_iff,
        inv_mul_cancel_left₀] using this
    have : x ∈ Ioo (0 : ℝ) 1 := by simpa [x, and_comm] using hθ'
    rw [← zpow_neg_one]
    refine (zpow_right_strictAnti₀ this.1 this.2).le_iff_ge.2 (Int.lt_add_one_iff.1 ?_); exact hn
  · rintro (rfl | H)
    exacts [circleIntegrable_zero_radius,
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
        H.symm.imp_left fun (hw : w ∉ sphere c |R|) =>
          sub_ne_zero.2 <| ne_of_mem_of_not_mem hz hw).circleIntegrable']

@[simp]
/-
**circleIntegrable_sub_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_sub_inv_iff {c w : Complex} {R : Real} : CircleIntegrable
 (fun z => (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ sphere c |R|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem circleIntegrable_sub_inv_iff {c w : ℂ} {R : ℝ} :
    CircleIntegrable (fun z => (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ sphere c |R| := by
  simp only [← zpow_neg_one, circleIntegrable_sub_zpow_iff]; simp

variable [NormedSpace ℂ E]

/-- Definition for $\oint_{|z-c|=R} f(z)\,dz$ -/
/-
**circleIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：circleIntegral (f : Complex -> E) (c : Complex) (R : Real) : E
参数：f : Complex -> E；c : Complex；R : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition for $\oint_{|z-c|=R} f(z)\,dz$
-/
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

/-- `∮ z in C(c, R), f z` is the circle integral $\oint_{|z-c|=R} f(z)\,dz$. -/
notation3 "∮ "(...)" in ""C("c", "R")"", "r:60:(scoped f => circleIntegral f c R) => r

/-
**circleIntegral_def_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegral_def_Icc (f : Complex -> E) (c : Complex) (R : Real) : (∮ z 
in C(c, R), f z) = ∫ θ in Icc 0 (2 * π), deriv (circleMap c R) θ • f (circleMap 
c R θ)
参数：f : Complex -> E；c : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleIntegral.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [ins
t_1 : NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   circleIntegral f c R = ∫ (
θ : ℝ) in…
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
-/
theorem circleIntegral_def_Icc (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π),
    deriv (circleMap c R) θ • f (circleMap c R θ) := by
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- If a sequence of continuous functions converges uniformly on the circle,
then their circle integrals converge to the circle integral of the limit function. -/
/-
**_root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：_root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn {ι : Type
*} {f : ι -> Complex -> E} {g : Complex -> E} {c : Complex} {R : Real} {l : Filt
er ι} [l.IsCountablyGenerated] (hR : 0 <= R) (hf : forallᶠ i in l, ContinuousOn 
(f i) (sphere c R)) (h : TendstoUniformlyOn f g l (sphere c R)) : Tendsto (fun n
 => ∮ z in C(c, R), f n z) l (𝓝 (∮ z in C(c, R), g z))
参数：hR : 0 <= R；hf : forallᶠ i in l, ContinuousOn (f i) (sphere c R)；h : TendstoU
niformlyOn f g l (sphere c R)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a sequence of continuous functions converges uniformly on the circle,
then their circle integrals converge to the circle integral of the limit functio
n.
-/
theorem _root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
    {ι : Type*} {f : ι → ℂ → E} {g : ℂ → E} {c : ℂ} {R : ℝ}
    {l : Filter ι} [l.IsCountablyGenerated] (hR : 0 ≤ R)
    (hf : ∀ᶠ i in l, ContinuousOn (f i) (sphere c R)) (h : TendstoUniformlyOn f g l (sphere c R)) :
    Tendsto (fun n ↦ ∮ z in C(c, R), f n z) l (𝓝 (∮ z in C(c, R), g z)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · refine hf.mono fun i hi ↦ .smul ?_ (hi.comp ?_ ?_)
    · rw [funext (deriv_circleMap _ _)]
      fun_prop
    · fun_prop
    · simp [hR, MapsTo]
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    simp only [dist_smul₀, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_nonneg hR, mul_one]
    intro ε hε
    rcases exists_pos_mul_lt hε R with ⟨δ, hδ₀, hRδ⟩
    refine (h δ hδ₀).mono fun i hi x hx ↦ ?_
    grw [← hRδ, hi (circleMap c R x) (by simp [hR])]

namespace circleIntegral

@[simp]
/-
**circleIntegral.integral_radius_zero** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`
。
形式化陈述：integral_radius_zero (f : Complex -> E) (c : Complex) : (∮ z in C(c, 0), f
 z) = 0
参数：f : Complex -> E；c : Complex。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `circleMap_zero_radius`：circleMap_zero_radius (c : Complex) : circleMap c
 0 = const Real c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_radius_zero (f : ℂ → E) (c : ℂ) : (∮ z in C(c, 0), f z) = 0 := by
  simp +unfoldPartialApp [circleIntegral, const]
/-
**circleIntegral.integral_congr** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_congr {f g : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R)
 (h : EqOn f g (sphere c R)) : (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z
参数：hR : 0 <= R；h : EqOn f g (sphere c R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleMap_mem_sphere`：circleMap_mem_sphere (c : Complex) {R : Real} (hR 
: 0 <= R) (θ : Real) : circleMap c R θ in sphere c R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : EqOn f g (sphere c R)) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z :=
  intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]

/-- Circle integrals are invariant when functions change along discrete sets. -/
/-
**circleIntegral.circleIntegral_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间
 `circleIntegral`。
形式化陈述：circleIntegral_congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : Co
mplex -> Complex} (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0)
 : (∮ z in C(c, R), f₁ z) = (∮ z in C(c, R), f₂ z)
参数：hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `ae_restrict_le_codiscreteWithin`：ae_restrict_le_codiscreteWithin {α : Ty
pe*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α] {μ : M
easure α} [NullSingle…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `trivial`：True
· 使用定理 `circleMap_preimage_codiscrete`：circleMap_preimage_codiscrete {c : Comple
x} {R : Real} (hR : R != 0) : map (circleMap c R) (codiscrete Real) <= codiscret
eWithin (sphere c |…

--- 原说明 ---
Circle integrals are invariant when functions change along discrete sets.
-/
theorem circleIntegral_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    (∮ z in C(c, R), f₁ z) = (∮ z in C(c, R), f₂ z) := by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)
/-
**circleIntegral.integral_sub_inv_smul_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 `circl
eIntegral`。
形式化陈述：integral_sub_inv_smul_sub_smul (f : Complex -> E) (c w : Complex) (R : Rea
l) : (∮ z in C(c, R), (z - w)⁻¹ • (z - w) • f z) = ∮ z in C(c, R), f z
参数：f : Complex -> E；c w : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleIntegral.integral_radius_zero`：integral_radius_zero (f : Complex -
> E) (c : Complex) : (∮ z in C(c, 0), f z) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Countable.preimage_circleMap`：Set.Countable.preimage_circleMap {s : 
Set Complex} (hs : s.Countable) (c : Complex) {R : Real} (hR : R != 0) : (circle
Map c R ⁻¹' s).Countab…
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Countable.ae_notMem`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingl
etonClass μ],…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem integral_sub_inv_smul_sub_smul (f : ℂ → E) (c w : ℂ) (R : ℝ) :
    (∮ z in C(c, R), (z - w)⁻¹ • (z - w) • f z) = ∮ z in C(c, R), f z := by
  rcases eq_or_ne R 0 with (rfl | hR); · simp only [integral_radius_zero]
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circleMap c hR
  refine intervalIntegral.integral_congr_ae ((this.ae_notMem _).mono fun θ hθ _' => ?_)
  change circleMap c R θ ≠ w at hθ
  simp only [inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]
/-
**circleIntegral.integral_undef** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_undef {f : Complex -> E} {c : Complex} {R : Real} (hf : ¬CircleIn
tegrable f c R) : (∮ z in C(c, R), f z) = 0
参数：hf : ¬CircleIntegrable f c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_undef`：∀ {E : Type u_5} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ}, ¬IntervalIn…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `circleIntegrable_iff`：circleIntegrable_iff [NormedSpace Complex E] {f : 
Complex -> E} {c : Complex} (R : Real) : CircleIntegrable f c R ↔ IntervalIntegr
able (fun …
-/
theorem integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)
/-
**circleIntegral.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_add {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleInt
egrable f c R) (hg : CircleIntegrable g c R) : (∮ z in C(c, R), f z + g z) = (∮ 
z in C(c, R), f z) + (∮ z in C(c, R), g z)
参数：hf : CircleIntegrable f c R；hg : CircleIntegrable g c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `intervalIntegral.integral_add`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f g : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ},   Interva…
· 使用定理 `CircleIntegrable.out`：out [NormedSpace Complex E] (hf : CircleIntegrable
 f c R) : IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circl
eMap c R θ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_add {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z + g z) = (∮ z in C(c, R), f z) + (∮ z in C(c, R), g z) := by
  simp only [circleIntegral, smul_add, intervalIntegral.integral_add hf.out hg.out]
/-
**circleIntegral.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_sub {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleInt
egrable f c R) (hg : CircleIntegrable g c R) : (∮ z in C(c, R), f z - g z) = (∮ 
z in C(c, R), f z) - ∮ z in C(c, R), g z
参数：hf : CircleIntegrable f c R；hg : CircleIntegrable g c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `CircleIntegrable.out`：out [NormedSpace Complex E] (hf : CircleIntegrable
 f c R) : IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circl
eMap c R θ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z - g z) = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z := by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]
/-
**circleIntegral.integral_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_fun_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E} {c : C
omplex} {R : Real} (h : forall i in s, CircleIntegrable (f i) c R) : (∮ z in C(c
, R), ∑ i in s, f i z) = ∑ i in s, ∮ z in C(c, R), f i z
参数：h : forall i in s, CircleIntegrable (f i) c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `intervalIntegral.integral_finsetSum`：∀ {E : Type u_5} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {μ : MeasureTheory.Measure ℝ}  
 {ι : Type u_8} {s : Fins…
· 使用定理 `CircleIntegrable.out`：out [NormedSpace Complex E] (hf : CircleIntegrable
 f c R) : IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circl
eMap c R θ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_fun_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum,
    intervalIntegral.integral_finsetSum fun i hi ↦ (h i hi).out]
/-
**circleIntegral.norm_integral_le_of_norm_le_const'** 是 Mathlib 中的一个定理，位于命名空间 `c
ircleIntegral`。
形式化陈述：norm_integral_le_of_norm_le_const' {f : Complex -> E} {c : Complex} {R C :
 Real} (hf : forall z in sphere c |R|, ‖f z‖ <= C) : ‖∮ z in C(c, R), f z‖ <= 2 
* π * |R| * C
参数：hf : forall z in sphere c |R|, ‖f z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `intervalIntegral.norm_integral_le_of_norm_le_const`：norm_integral_le_of_
norm_le_const {a b C : Real} {f : Real -> E} (h : forall x in Ι a b, ‖f x‖ <= C)
 : ‖∫ x in a..b, f x‖ <= C * |b - a|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem norm_integral_le_of_norm_le_const' {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hf : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C :=
  calc
    ‖∮ z in C(c, R), f z‖ ≤ |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ ≤ |R| * C := by
            gcongr; exact hf _ <| circleMap_mem_sphere' _ _ _
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl
/-
**circleIntegral.norm_integral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `ci
rcleIntegral`。
形式化陈述：norm_integral_le_of_norm_le_const {f : Complex -> E} {c : Complex} {R C : 
Real} (hR : 0 <= R) (hf : forall z in sphere c R, ‖f z‖ <= C) : ‖∮ z in C(c, R),
 f z‖ <= 2 * π * R * C
参数：hR : 0 <= R；hf : forall z in sphere c R, ‖f z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `circleIntegral.norm_integral_le_of_norm_le_const'`：norm_integral_le_of_n
orm_le_const' {f : Complex -> E} {c : Complex} {R C : Real} (hf : forall z in sp
here c |R|, ‖f z‖ <= C) : ‖∮ z in C(c, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem norm_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * R * C :=
  have : |R| = R := abs_of_nonneg hR
  calc
    ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C := norm_integral_le_of_norm_le_const' <| by rwa [this]
    _ = 2 * π * R * C := by rw [this]
/-
**circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const** 是 Mathlib
 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：norm_two_pi_i_inv_smul_integral_le_of_norm_le_const {f : Complex -> E} {c 
: Complex} {R C : Real} (hR : 0 <= R) (hf : forall z in sphere c R, ‖f z‖ <= C) 
: ‖(2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), f z‖ <= R * C
参数：hR : 0 <= R；hf : forall z in sphere c R, ‖f z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用引理 `Complex.norm_ofNat`：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : C
omplex)‖ = OfNat.ofNat n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 36 条，此处仅展示前 30 条）
-/
theorem norm_two_pi_i_inv_smul_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hR : 0 ≤ R) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), f z‖ ≤ R * C := by
  have : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by simp [Real.pi_pos.le]
  rw [norm_smul, this, ← div_eq_inv_mul, div_le_iff₀ Real.two_pi_pos, mul_comm (R * C), ← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

/-- If `f` is continuous on the circle `|z - c| = R`, `R > 0`, the `‖f z‖` is less than or equal to
`C : ℝ` on this circle, and this norm is strictly less than `C` at some point `z` of the circle,
then `‖∮ z in C(c, R), f z‖ < 2 * π * R * C`. -/
/-
**circleIntegral.norm_integral_lt_of_norm_le_const_of_lt** 是 Mathlib 中的一个定理，位于命名
空间 `circleIntegral`。
形式化陈述：norm_integral_lt_of_norm_le_const_of_lt {f : Complex -> E} {c : Complex} {
R C : Real} (hR : 0 < R) (hc : ContinuousOn f (sphere c R)) (hf : forall z in sp
here c R, ‖f z‖ <= C) (hlt : exists z in sphere c R, ‖f z‖ < C) : ‖∮ z in C(c, R
), f z‖ < 2 * π * R * C
参数：hR : 0 < R；hc : ContinuousOn f (sphere c R)；hf : forall z in sphere c R, ‖f z
‖ <= C；hlt : exists z in sphere c R, ‖f z‖ < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `image_circleMap_Ioc`：image_circleMap_Ioc (c : Complex) (R : Real) : circ
leMap c R '' Ioc 0 (2 * π) = sphere c |R|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `intervalIntegral.norm_integral_le_integral_norm`：norm_integral_le_integr
al_norm (h : a <= b) : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in a..b, ‖f x‖ ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
`：integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : Real -> Real} {
a b : Real} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hg…
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is continuous on the circle `|z - c| = R`, `R > 0`, the `‖f z‖` is less t
han or equal to
`C : ℝ` on this circle, and this norm is strictly less than `C` at some point `z
` of the circle,
then `‖∮ z in C(c, R), f z‖ < 2 * π * R * C`.
-/
theorem norm_integral_lt_of_norm_le_const_of_lt {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hc : ContinuousOn f (sphere c R)) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C)
    (hlt : ∃ z ∈ sphere c R, ‖f z‖ < C) : ‖∮ z in C(c, R), f z‖ < 2 * π * R * C := by
  rw [← _root_.abs_of_pos hR, ← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ ≤ ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in 0..2 * π, R * C := by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_I,
        mul_one]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · gcongr
        exact hf _ <| circleMap_mem_sphere _ hR.le _
      · gcongr
    _ = 2 * π * R * C := by simp [mul_assoc]; ring

@[simp]
/-
**circleIntegral.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Co
mplex E] (a : 𝕜) (f : Complex -> E) (c : Complex) (R : Real) : (∮ z in C(c, R), 
a • f z) = a • ∮ z in C(c, R), f z
参数：a : 𝕜；f : Complex -> E；c : Complex；R : Real。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
    (f : ℂ → E) (c : ℂ) (R : ℝ) : (∮ z in C(c, R), a • f z) = a • ∮ z in C(c, R), f z := by
  simp only [circleIntegral, ← smul_comm a (_ : ℂ) (_ : E), intervalIntegral.integral_smul]

@[simp]
/-
**circleIntegral.integral_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_smul_const [CompleteSpace E] (f : Complex -> Complex) (a : E) (c 
: Complex) (R : Real) : (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a
参数：f : Complex -> Complex；a : E；c : Complex；R : Real。
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
· 使用定理 `intervalIntegral.integral_smul_const`：∀ {E : Type u_5} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {μ : MeasureTheory.Measure ℝ} 
  [CompleteSpace E] {𝕜 : T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_smul_const [CompleteSpace E] (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a := by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]

@[simp]
/-
**circleIntegral.integral_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegral`。
形式化陈述：integral_const_mul (a : Complex) (f : Complex -> Complex) (c : Complex) (R
 : Real) : (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z
参数：a : Complex；f : Complex -> Complex；c : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `circleIntegral.integral_smul`：integral_smul {𝕜 : Type*} [RCLike 𝕜] [Norm
edSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜) (f : Complex -> E) (c : Complex
) (R : Real) : (∮ …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z :=
  integral_smul a f c R

@[simp]
/-
**circleIntegral.integral_sub_center_inv** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegr
al`。
形式化陈述：integral_sub_center_inv (c : Complex) {R : Real} (hR : R != 0) : (∮ z in C
(c, R), (z - c)⁻¹) = 2 * π * I
参数：c : Complex；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `circleMap_sub_center`：circleMap_sub_center (c : Complex) (R : Real) (θ :
 Real) : circleMap c R θ - c = circleMap 0 R θ
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `circleMap_ne_center`：circleMap_ne_center {c : Complex} {R : Real} (hR : 
R != 0) {θ : Real} : circleMap c R θ != c
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I := by
  simp [circleIntegral, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center hR)]

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`. -/
/-
**circleIntegral.integral_eq_zero_of_hasDerivWithinAt'** 是 Mathlib 中的一个定理，位于命名空间
 `circleIntegral`。
形式化陈述：integral_eq_zero_of_hasDerivWithinAt' [CompleteSpace E] {f f' : Complex ->
 E} {c : Complex} {R : Real} (h : forall z in sphere c |R|, HasDerivWithinAt f (
f' z) (sphere c |R|) z) : (∮ z in C(c, R), f' z) = 0
参数：h : forall z in sphere c |R|, HasDerivWithinAt f (f' z) (sphere c |R|) z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
f : α → β} {c : α} [inst : Add α],   Function.Periodic f c → ∀ (g : β → γ), Func
tion.Periodi…
· 使用定理 `periodic_circleMap`：periodic_circleMap (c : Complex) (R : Real) : Period
ic (circleMap c R) (2 * π)
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt`：integral_eq_sub_of_hasDe
rivAt (hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalInt
egrable f' volume a b) : ∫ y in a..b…
· 使用定理 `HasDerivWithinAt.scomp_hasDerivAt`：HasDerivWithinAt.scomp_hasDerivAt (hg
 : HasDerivWithinAt g₁ g₁' s' (h x)) (hh : HasDerivAt h h' x) (hs : forall x, h 
x in s') : HasDerivAt (…
· 使用定理 `circleMap_mem_sphere'`：circleMap_mem_sphere' (c : Complex) (R : Real) (θ
 : Real) : circleMap c R θ in sphere c |R|
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `differentiable_circleMap`：differentiable_circleMap (c : Complex) (R : Re
al) : Differentiable Real (circleMap c R)
· 使用定理 `CircleIntegrable.out`：out [NormedSpace Complex E] (hf : CircleIntegrable
 f c R) : IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circl
eMap c R θ…
· 使用定理 `circleIntegral.integral_undef`：integral_undef {f : Complex -> E} {c : Co
mplex} {R : Real} (hf : ¬CircleIntegrable f c R) : (∮ z in C(c, R), f z) = 0

--- 原说明 ---
If `f' : ℂ → E` is a derivative of a complex differentiable function on the circ
le
`Metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`.
-/
theorem integral_eq_zero_of_hasDerivWithinAt' [CompleteSpace E] {f f' : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ sphere c |R|, HasDerivWithinAt f (f' z) (sphere c |R|) z) :
    (∮ z in C(c, R), f' z) = 0 := by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`. -/
/-
**circleIntegral.integral_eq_zero_of_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 
`circleIntegral`。
形式化陈述：integral_eq_zero_of_hasDerivWithinAt [CompleteSpace E] {f f' : Complex -> 
E} {c : Complex} {R : Real} (hR : 0 <= R) (h : forall z in sphere c R, HasDerivW
ithinAt f (f' z) (sphere c R) z) : (∮ z in C(c, R), f' z) = 0
参数：hR : 0 <= R；h : forall z in sphere c R, HasDerivWithinAt f (f' z) (sphere c R
) z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `circleIntegral.integral_eq_zero_of_hasDerivWithinAt'`：integral_eq_zero_o
f_hasDerivWithinAt' [CompleteSpace E] {f f' : Complex -> E} {c : Complex} {R : R
eal} (h : forall z in sphere c |R|, HasDer…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `f' : ℂ → E` is a derivative of a complex differentiable function on the circ
le
`Metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`.
-/
theorem integral_eq_zero_of_hasDerivWithinAt [CompleteSpace E]
    {f f' : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R, HasDerivWithinAt f (f' z) (sphere c R) z) : (∮ z in C(c, R), f' z) = 0 :=
  integral_eq_zero_of_hasDerivWithinAt' <| (abs_of_nonneg hR).symm ▸ h

/-- If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on the circle with
center `c` and radius `|R|`, so the integral `∮ z in C(c, R), (z - w) ^ n` is equal to zero. -/
/-
**circleIntegral.integral_sub_zpow_of_undef** 是 Mathlib 中的一个定理，位于命名空间 `circleInt
egral`。
形式化陈述：integral_sub_zpow_of_undef {n : Int} {c w : Complex} {R : Real} (hn : n < 
0) (hw : w in sphere c |R|) : (∮ z in C(c, R), (z - w) ^ n) = 0
参数：hn : n < 0；hw : w in sphere c |R|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `circleIntegral.integral_radius_zero`：integral_radius_zero (f : Complex -
> E) (c : Complex) : (∮ z in C(c, 0), f z) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `circleIntegral.integral_undef`：integral_undef {f : Complex -> E} {c : Co
mplex} {R : Real} (hf : ¬CircleIntegrable f c R) : (∮ z in C(c, R), f z) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] 
{a b : E} {r : ℝ}, b ∈ Metric.sphere a r ↔ ‖b - a‖ = r

--- 原说明 ---
If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on t
he circle with
center `c` and radius `|R|`, so the integral `∮ z in C(c, R), (z - w) ^ n` is eq
ual to zero.
-/
theorem integral_sub_zpow_of_undef {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0)
    (hw : w ∈ sphere c |R|) : (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or] using mem_sphere_iff_norm.1 hw

/-- If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
/-
**circleIntegral.integral_sub_zpow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `circleIntegr
al`。
形式化陈述：integral_sub_zpow_of_ne {n : Int} (hn : n != -1) (c w : Complex) (R : Real
) : (∮ z in C(c, R), (z - w) ^ n) = 0
参数：hn : n != -1；c w : Complex；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `circleIntegral.integral_sub_zpow_of_undef`：integral_sub_zpow_of_undef {n
 : Int} {c w : Complex} {R : Real} (hn : n < 0) (hw : w in sphere c |R|) : (∮ z 
in C(c, R), (z - w) ^ n) = 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_zpow`：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
 : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the ci
rcle equals
zero.
-/
theorem integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
    (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  by_cases! H : w ∈ sphere c |R| ∧ n < -1
  · rcases H with ⟨hw, hn⟩
    exact integral_sub_zpow_of_undef (hn.trans (by decide)) hw
  have hd : ∀ z, z ≠ w ∨ -1 ≤ n →
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert!
      ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z ((hasDerivAt_id z).sub_const w)).div_const
        _ using 1
    · have hn' : (n + 1 : ℂ) ≠ 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z ?_).hasDerivWithinAt
  exact (ne_or_eq z w).imp_right fun (h : z = w) => H <| h ▸ hz

end circleIntegral

/-- The power series that is equal to
$\frac{1}{2πi}\sum_{n=0}^{\infty}
  \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `f`, this power
series converges to the Cauchy integral for `f`. -/
/-
**cauchyPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cauchyPowerSeries (f : Complex -> E) (c : Complex) (R : Real) : FormalMult
ilinearSeries Complex Complex E
参数：f : Complex -> E；c : Complex；R : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series that is equal to
$\frac{1}{2πi}\sum_{n=0}^{\infty}
  \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R
`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `Metric.cl
osedBall c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `
f`, this power
series converges to the Cauchy integral for `f`.
-/
def cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ) : FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiRing ℂ _ <|
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z
/-
**cauchyPowerSeries_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchyPowerSeries_apply (f : Complex -> E) (c : Complex) (R : Real) (n : N
at) (w : Complex) : (cauchyPowerSeries f c R n fun _ => w) = (2 * π * I : Comple
x)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z
参数：f : Complex -> E；c : Complex；R : Real；n : Nat；w : Complex。
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
· 使用定理 `Fin.prod_const`：prod_const (n : Nat) (x : M) : ∏ _i : Fin n, x = x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `circleIntegral.integral_smul`：integral_smul {𝕜 : Type*} [RCLike 𝕜] [Norm
edSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜) (f : Complex -> E) (c : Complex
) (R : Real) : (∮ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem cauchyPowerSeries_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries f c R n fun _ => w) =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    div_eq_mul_inv, mul_pow, mul_smul, circleIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]
/-
**norm_cauchyPowerSeries_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_cauchyPowerSeries_le (f : Complex -> E) (c : Complex) (R : Real) (n :
 Nat) : ‖cauchyPowerSeries f c R n‖ <= ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (
circleMap c R θ)‖) * |R|⁻¹ ^ n
参数：f : Complex -> E；c : Complex；R : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.mkPiRing.congr_simp`：∀ (R : Type u) (ι : Type v
) {M : Type u_1} [inst : Fintype ι] [inst_1 : CommRing R] [inst_2 : AddCommMonoi
d M]   [inst_3 : _root_.Module R M…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `ContinuousMultilinearMap.norm_mkPiRing`：norm_mkPiRing (z : G) : ‖Continu
ousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用引理 `Complex.norm_ofNat`：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : C
omplex)‖ = OfNat.ofNat n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
（共 79 条，此处仅展示前 30 条）
-/
theorem norm_cauchyPowerSeries_le (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖ ≤
      ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n :=
  calc ‖cauchyPowerSeries f c R n‖
    _ = (2 * π)⁻¹ * ‖∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp [cauchyPowerSeries, norm_smul, Real.pi_pos.le]
    _ ≤ (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ •
        (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = (2 * π)⁻¹ *
        (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ x : ℝ in 0..2 * π, ‖f (circleMap c R x)‖))) := by
      simp [norm_smul, mul_left_comm |R|]
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev]
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)]
        rwa [Ne, _root_.abs_eq_zero]
/-
**le_radius_cauchyPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_radius_cauchyPowerSeries (f : Complex -> E) (c : Complex) (R : Real>=0)
 : ↑R <= (cauchyPowerSeries f c R).radius
参数：f : Complex -> E；c : Complex；R : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_cauchyPowerSeries_le`：norm_cauchyPowerSeries_le (f : Complex -> E) 
(c : Complex) (R : Real) (n : Nat) : ‖cauchyPowerSeries f c R n‖ <= ((2 * π)⁻¹ *
 ∫ θ : Real in …
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `intervalIntegral.integral_nonneg`：integral_nonneg (hab : a <= b) (hf : f
orall u, u in Icc a b -> 0 <= f u) : 0 <= ∫ u in a..b, f u ∂μ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
（共 33 条，此处仅展示前 30 条）
-/
theorem le_radius_cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ≥0) :
    ↑R ≤ (cauchyPowerSeries f c R).radius := by
  refine
    (cauchyPowerSeries f c R).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans ?_
  rw [abs_of_nonneg R.coe_nonneg]
  rcases eq_or_ne (R ^ n : ℝ) 0 with hR | hR
  · rw_mod_cast [hR, mul_zero]
    exact mul_nonneg (inv_nonneg.2 Real.two_pi_pos.le)
      (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  · rw [inv_pow]
    have : (R : ℝ) ^ n ≠ 0 := by norm_cast at hR ⊢
    rw [inv_mul_cancel_right₀ this]

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc
`Metric.ball c R`. -/
/-
**hasSum_two_pi_I_cauchyPowerSeries_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_two_pi_I_cauchyPowerSeries_integral {f : Complex -> E} {c : Complex
} {R : Real} {w : Complex} (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) : HasSum
 (fun n : Nat => ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z) (∮ z in C(
c, R), (z - (c + w))⁻¹ • f z)
参数：hf : CircleIntegrable f c R；hw : ‖w‖ < R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `intervalIntegral.hasSum_integral_of_dominated_convergence`：∀ {E : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → 
E}   {μ : MeasureTheory.Measure ℝ} {ι : Type u_…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `measurable_circleMap`：measurable_circleMap (c : Complex) (R : Real) : Me
asurable (circleMap c R)
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
For any circle integrable function `f`, the power series `cauchyPowerSeries f c 
R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
 disc
`Metric.ball c R`.
-/
theorem hasSum_two_pi_I_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n : ℕ => ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z)
      (∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hwR : ‖w‖ / R ∈ Ico (0 : ℝ) 1 :=
    ⟨div_nonneg (norm_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (‖w‖ / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    · fun_prop
    · fun_prop
    · fun_prop
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, inv_mul_cancel_left₀ hR.ne', mul_comm ‖_‖]
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖w / (circleMap c R θ - c)‖ < 1 := by simpa [abs_of_pos hR] using hwR.2
    convert! (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    simp [← sub_sub, ← mul_inv, sub_mul, div_mul_cancel₀ _ (circleMap_ne_center hR.ne')]

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
/-
**hasSum_cauchyPowerSeries_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_cauchyPowerSeries_integral {f : Complex -> E} {c : Complex} {R : Re
al} {w : Complex} (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) : HasSum (fun n =
> cauchyPowerSeries f c R n fun _ => w) ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R
), (z - (c + w))⁻¹ • f z)
参数：hf : CircleIntegrable f c R；hw : ‖w‖ < R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `cauchyPowerSeries_apply`：cauchyPowerSeries_apply (f : Complex -> E) (c :
 Complex) (R : Real) (n : Nat) (w : Complex) : (cauchyPowerSeries f c R n fun _ 
=> w) = (2 * …
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `hasSum_two_pi_I_cauchyPowerSeries_integral`：hasSum_two_pi_I_cauchyPowerS
eries_integral {f : Complex -> E} {c : Complex} {R : Real} {w : Complex} (hf : C
ircleIntegrable f c R) (hw : ‖w‖…

--- 原说明 ---
For any circle integrable function `f`, the power series `cauchyPowerSeries f c 
R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ 
• f z` on the open
disc `Metric.ball c R`.
-/
theorem hasSum_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n => cauchyPowerSeries f c R n fun _ => w)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
/-
**sum_cauchyPowerSeries_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_cauchyPowerSeries_eq_integral {f : Complex -> E} {c : Complex} {R : Re
al} {w : Complex} (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) : (cauchyPowerSer
ies f c R).sum w = (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f
 z
参数：hf : CircleIntegrable f c R；hw : ‖w‖ < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_cauchyPowerSeries_integral`：hasSum_cauchyPowerSeries_integral {f 
: Complex -> E} {c : Complex} {R : Real} {w : Complex} (hf : CircleIntegrable f 
c R) (hw : ‖w‖ < R) : H…

--- 原说明 ---
For any circle integrable function `f`, the power series `cauchyPowerSeries f c 
R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ 
• f z` on the open
disc `Metric.ball c R`.
-/
theorem sum_cauchyPowerSeries_eq_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    (cauchyPowerSeries f c R).sum w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z :=
  (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
/-
**hasFPowerSeriesOn_cauchy_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesOn_cauchy_integral {f : Complex -> E} {c : Complex} {R : Re
al>=0} (hf : CircleIntegrable f c R) (hR : 0 < R) : HasFPowerSeriesOnBall (fun w
 => (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (cauchyPowerSerie
s f c R) c R
参数：hf : CircleIntegrable f c R；hR : 0 < R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_radius_cauchyPowerSeries`：le_radius_cauchyPowerSeries (f : Complex ->
 E) (c : Complex) (R : Real>=0) : ↑R <= (cauchyPowerSeries f c R).radius
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `hasSum_cauchyPowerSeries_integral`：hasSum_cauchyPowerSeries_integral {f 
: Complex -> E} {c : Complex} {R : Real} {w : Complex} (hf : CircleIntegrable f 
c R) (hw : ‖w‖ < R) : H…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖

--- 原说明 ---
For any circle integrable function `f`, the power series `cauchyPowerSeries f c 
R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ 
• f z` on the open
disc `Metric.ball c R`.
-/
theorem hasFPowerSeriesOn_cauchy_integral {f : ℂ → E} {c : ℂ} {R : ℝ≥0}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    HasFPowerSeriesOnBall (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z)
      (cauchyPowerSeries f c R) c R :=
  { r_le := le_radius_cauchyPowerSeries _ _ _
    r_pos := ENNReal.coe_pos.2 hR
    hasSum := fun hy ↦ hasSum_cauchyPowerSeries_integral hf <| by simpa using hy }

namespace circleIntegral

/-- Integral $\oint_{|z-c|=R} \frac{dz}{z-w} = 2πi$ whenever $|w-c| < R$. -/
/-
**circleIntegral.integral_sub_inv_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `circleI
ntegral`。
形式化陈述：integral_sub_inv_of_mem_ball {c w : Complex} {R : Real} (hw : w in ball c 
R) : (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I
参数：hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `circleIntegral.integral_sub_zpow_of_ne`：integral_sub_zpow_of_ne {n : Int
} (hn : n != -1) (c w : Complex) (R : Real) : (∮ z in C(c, R), (z - w) ^ n) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `circleIntegral.integral_sub_center_inv`：integral_sub_center_inv (c : Com
plex) {R : Real} (hR : R != 0) : (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `circleIntegral.integral_const_mul`：integral_const_mul (a : Complex) (f :
 Complex -> Complex) (c : Complex) (R : Real) : (∮ z in C(c, R), a * f z) = a * 
∮ z in C(c, R), f z
· 使用定理 `circleIntegral.integral_congr`：integral_congr {f g : Complex -> E} {c : 
Complex} {R : Real} (hR : 0 <= R) (h : EqOn f g (sphere c R)) : (∮ z in C(c, R),
 f z) = ∮ z in C(c,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Integral $\oint_{|z-c|=R} \frac{dz}{z-w} = 2πi$ whenever $|w-c| < R$.
-/
theorem integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : ℕ => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : ℂ)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A (mem_ball_iff_norm.1 hw)
  have H : ∀ n : ℕ, n ≠ 0 → (∮ z in C(c, R), (z - c) ^ (-n - 1 : ℤ)) = 0 := by
    refine fun n hn => integral_sub_zpow_of_ne ?_ _ _ _; simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by simp [hR.ne']
  refine this ▸ hasSum_single _ fun n hn => ?_
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn), mul_zero]
  intro z _
  rw [← pow_succ, ← zpow_natCast, inv_zpow, ← zpow_neg, Int.natCast_succ, neg_add,
    sub_eq_add_neg _ (1 : ℤ)]

end circleIntegral

