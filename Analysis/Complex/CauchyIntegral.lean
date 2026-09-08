/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Cauchy integral formula

In this file we prove the Cauchy-Goursat theorem and the Cauchy integral formula for integrals over
circles. Most results are formulated for a function `f : ℂ → E` that takes values in a complex
Banach space with second countable topology.

## Main statements

In the following theorems, if the name ends with `off_countable`, then the actual theorem assumes
differentiability at all but countably many points of the set mentioned below.

### Rectangle integrals

* `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and *real* differentiable on its interior, then
  its integral over the boundary of this rectangle is equal to the integral of
  `I • f' (x + y * I) 1 - f' (x + y * I) I` over the rectangle, where `f' z w : E` is the derivative
  of `f` at `z` in the direction `w` and `I = Complex.I` is the imaginary unit.

* `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and is *complex* differentiable on its interior,
  then its integral over the boundary of this rectangle is equal to zero.

### Annuli and circles

* `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: If a
  function `f : ℂ → E` is continuous on a closed annulus `{z | r ≤ |z - c| ≤ R}` and is complex
  differentiable on its interior `{z | r < |z - c| < R}`, then the integrals of `(z - c)⁻¹ • f z`
  over the outer boundary and over the inner boundary are equal.

* `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`,
  `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`:
  If a function `f : ℂ → E` is continuous on a punctured closed disc `{z | |z - c| ≤ R ∧ z ≠ c}`, is
  complex differentiable on the corresponding punctured open disc, and tends to `y` as `z → c`,
  `z ≠ c`, then the integral of `(z - c)⁻¹ • f z` over the circle `|z - c| = R` is equal to
  `2πiy`. In particular, if `f` is continuous on the whole closed disc and is complex differentiable
  on the corresponding open disc, then this integral is equal to `2πif(c)`.

* `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`,
  `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
  complex differentiable on the corresponding open disc, then for any `w` in the corresponding open
  disc the integral of `(z - w)⁻¹ • f z` over the boundary of the disc is equal to `2πif(w)`.
  Two versions of the lemma put the multiplier `2πi` at the different sides of the equality.

### Analyticity

* `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`: If `f : ℂ → E` is continuous
  on a closed disc of positive radius and is complex differentiable on the corresponding open disc,
  then it is analytic on the corresponding open disc, and the coefficients of the power series are
  given by Cauchy integral formulas.

* `DifferentiableOn.hasFPowerSeriesOnBall`: If `f : ℂ → E` is complex differentiable on a
  closed disc of positive radius, then it is analytic on the corresponding open disc, and the
  coefficients of the power series are given by Cauchy integral formulas.

* `DifferentiableOn.analyticAt`, `Differentiable.analyticAt`: If `f : ℂ → E` is differentiable
  on a neighborhood of a point, then it is analytic at this point. In particular, if `f : ℂ → E`
  is differentiable on the whole `ℂ`, then it is analytic at every point `z : ℂ`.

* `Differentiable.hasFPowerSeriesOnBall`: If `f : ℂ → E` is differentiable everywhere then the
  `cauchyPowerSeries f z R` is a formal power series representing `f` at `z` with infinite
  radius of convergence (this holds for any choice of `0 < R`).

### Higher derivatives

* `Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula for derivatives**: formula for the higher derivatives of `f` at the
  centre `c` of a disc in terms of circle integrals of `f w / (w - c) ^ (n + 1)` around the
  boundary circle.

## Implementation details

The proof of the Cauchy integral formula in this file is based on a very general version of the
divergence theorem, see `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
(a version for functions defined on `Fin (n + 1) → ℝ`),
`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivWithinAt_off_countable_of_le`, and
`MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable` (versions for
functions defined on `ℝ × ℝ`).

Usually, the divergence theorem is formulated for a $C^1$ smooth function. The theorems formulated
above deal with a function that is

* continuous on a closed box/rectangle;
* differentiable at all but countably many points of its interior;
* have divergence integrable over the closed box/rectangle.

First, we reformulate the theorem for a *real*-differentiable map `ℂ → E`, and relate the integral
of `f` over the boundary of a rectangle in `ℂ` to the integral of the derivative
$\frac{\partial f}{\partial \bar z}$ over the interior of this box. In particular, for a *complex*
differentiable function, the latter derivative is zero, hence the integral over the boundary of a
rectangle is zero. Thus we get the Cauchy-Goursat theorem for a rectangle in `ℂ`.

Next, we apply this theorem to the function $F(z)=f(c+e^{z})$ on the rectangle
$[\ln r, \ln R]\times [0, 2\pi]$ to prove that
$$
  \oint_{|z-c|=r}\frac{f(z)\,dz}{z-c}=\oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}
$$
provided that `f` is continuous on the closed annulus `r ≤ |z - c| ≤ R` and is complex
differentiable on its interior `r < |z - c| < R` (possibly, at all but countably many points).

Here and below, we write $\frac{f(z)}{z-c}$ in the documentation while the actual lemmas use
`(z - c)⁻¹ • f z` because `f z` belongs to some Banach space over `ℂ` and `f z / (z - c)` is
undefined.

Taking the limit of this equality as `r` tends to `𝓝[>] 0`, we prove
$$
  \oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}=2\pi if(c)
$$
provided that `f` is continuous on the closed disc `|z - c| ≤ R` and is differentiable at all but
countably many points of its interior. This is the Cauchy integral formula for the center of a
circle. In particular, if we apply this function to `F z = (z - c) • f z`, then we get
$$
  \oint_{|z-c|=R} f(z)\,dz=0.
$$

In order to deduce the Cauchy integral formula for any point `w`, `|w - c| < R`, we consider the
slope function `g : ℂ → E` given by `g z = (z - w)⁻¹ • (f z - f w)` if `z ≠ w` and `g w = f' w`.
This function satisfies assumptions of the previous theorem, so we have
$$
  \oint_{|z-c|=R} \frac{f(z)\,dz}{z-w}=\oint_{|z-c|=R} \frac{f(w)\,dz}{z-w}=
  \left(\oint_{|z-c|=R} \frac{dz}{z-w}\right)f(w).
$$
The latter integral was computed in `circleIntegral.integral_sub_inv_of_mem_ball` and is equal to
`2 * π * Complex.I`.

There is one more step in the actual proof. Since we allow `f` to be non-differentiable on a
countable set `s`, we cannot immediately claim that `g` is continuous at `w` if `w ∈ s`. So, we use
the proof outlined in the previous paragraph for `w ∉ s` (see
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux`), then use continuity
of both sides of the formula and density of `sᶜ` to prove the formula for all points of the open
ball, see `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`.

Finally, we use the properties of the Cauchy integrals established elsewhere (see
`hasFPowerSeriesOn_cauchy_integral`) and Cauchy integral formula to prove that the original
function is analytic on the open ball.

## Tags

Cauchy-Goursat theorem, Cauchy integral formula
-/

public section

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function

open scoped Interval Real NNReal ENNReal Topology

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Complex

section rectangle
/-!
## Functions on rectangles
-/

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corresponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
/-
**Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable** 是 Mathlib 中
的一个定理，位于命名空间 `Complex`。
形式化陈述：integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : Complex -> E
) (f' : Complex -> Complex ->L[Real] E) (z w : Complex) (s : Set Complex) (hs : 
s.Countable) (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]])) (Hd 
: forall x in Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (
max z.im w.im) \ s, HasFDerivAt f (f' x) x) (Hi : IntegrableOn (fun z => I • f' 
z 1 - f' z I) ([[z.re, w.re]] ×Complex [[z.im, w.im]])) : (∫ x : Real in z.re..w
.re, f (x + z.im * I)) - (
参数：f : Complex -> E；f' : Complex -> Complex ->L[Real] E；z w : Complex；s : Set Co
mplex；hs : s.Countable；Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im
]])；Hd : forall x in Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im 
w.im) (max z.im w.im) \ s, HasFDerivAt f (f' x) x；Hi : IntegrableOn (fun z => I 
• f' z 1 - f' z I) ([[z.re, w.re]] ×Complex [[z.im, w.im]])。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.mk_eq_add_mul_I`：mk_eq_add_mul_I (a b : Real) : Complex.mk a b =
 a + b * I
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `ContinuousLinearEquiv.continuousOn`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [i
nst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   
[inst_2 : RingHomInvPair…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable`：in
tegral2_divergence_prod_of_hasFDerivAt_off_countable (f g : Real × Real -> E) (f
' g' : Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opp
osite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corr
esponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectan
gle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\part
ial f}{\partial y}$
over the rectangle.
-/
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I := by
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equivRealProdCLM.symm
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : ℝ × ℝ → E := f ∘ e
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fun p => (f' (e p)).comp (e : ℝ × ℝ →L[ℝ] ℂ)
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I) := by
    rintro ⟨x, y⟩
    simp only [F', neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, he₁, he₂, neg_add_eq_sub, neg_sub]
  set R : Set (ℝ × ℝ) := [[z.re, w.re]] ×ˢ [[w.im, z.im]]
  set t : Set (ℝ × ℝ) := e ⁻¹' s
  rw [uIcc_comm z.im] at Hc Hi; rw [min_comm z.im, max_comm z.im] at Hd
  have hR : e ⁻¹' ([[z.re, w.re]] ×ℂ [[w.im, z.im]]) = R := rfl
  have htc : ContinuousOn F R := Hc.comp e.continuousOn hR.ge
  have htd :
    ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t,
      HasFDerivAt F (F' p) p :=
    fun p hp => (Hd (e p) hp).comp p e.hasFDerivAt
  simp_rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm w.im z.im, ←
    intervalIntegral.integral_neg, ← hF']
  refine (integral2_divergence_prod_of_hasFDerivAt_off_countable (fun p => -(I • F p)) F
    (fun p => -(I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
    (htc.const_smul _).neg htc (fun p hp => ((htd p hp).const_smul I).neg) htd ?_).symm
  rw [← (volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)] at Hi
  simpa only [hF'] using! Hi.neg

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the integral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
/-
**Complex.integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real** 是 Mathlib
 中的一个定理，位于命名空间 `Complex`。
形式化陈述：integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real (f : Complex ->
 E) (f' : Complex -> Complex ->L[Real] E) (z w : Complex) (Hc : ContinuousOn f (
[[z.re, w.re]] ×Complex [[z.im, w.im]])) (Hd : forall x in Ioo (min z.re w.re) (
max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im), HasFDerivAt f (f' x
) x) (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×Complex 
[[z.im, w.im]])) : (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in
 z.re..w.re, f (x + w.im *
参数：f : Complex -> E；f' : Complex -> Complex ->L[Real] E；z w : Complex；Hc : Conti
nuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]])；Hd : forall x in Ioo (min z.r
e w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im), HasFDerivA
t f (f' x) x；Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×C
omplex [[z.im, w.im]])。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`：integr
al_boundary_rect_of_hasFDerivAt_real_off_countable (f : Complex -> E) (f' : Comp
lex -> Complex ->L[Real] E) (z w : Complex) (s : Set C…
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opp
osite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the i
ntegral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\part
ial f}{\partial y}$
over the rectangle.
-/
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi

/-- Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectangle with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
/-
**Complex.integral_boundary_rect_of_differentiableOn_real** 是 Mathlib 中的一个定理，位于命
名空间 `Complex`。
形式化陈述：integral_boundary_rect_of_differentiableOn_real (f : Complex -> E) (z w : 
Complex) (Hd : DifferentiableOn Real f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
 (Hi : IntegrableOn (fun z => I • fderiv Real f z 1 - fderiv Real f z I) ([[z.re
, w.re]] ×Complex [[z.im, w.im]])) : (∫ x : Real in z.re..w.re, f (x + z.im * I)
) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) + I • (∫ y : Real in z.im..w.im
, f (re w + y * I)) - I • (∫ y : Real in z.im..w.im, f (re z + y * I)) = ∫ x : R
eal in z.re..w.re, ∫ y : R
参数：f : Complex -> E；z w : Complex；Hd : DifferentiableOn Real f ([[z.re, w.re]] ×
Complex [[z.im, w.im]])；Hi : IntegrableOn (fun z => I • fderiv Real f z 1 - fder
iv Real f z I) ([[z.re, w.re]] ×Complex [[z.im, w.im]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`：integr
al_boundary_rect_of_hasFDerivAt_real_off_countable (f : Complex -> E) (f' : Comp
lex -> Complex ->L[Real] E) (z w : Complex) (s : Set C…
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DifferentiableOn.hasFDerivAt`：DifferentiableOn.hasFDerivAt (h : Differen
tiableOn 𝕜 f s) (hs : s in 𝓝 x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.interior_reProdIm`：interior_reProdIm (s t : Set Real) : interior
 (s ×Complex t) = interior s ×Complex interior t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectang
le with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on t
his rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral 
of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\part
ial f}{\partial y}$
over the rectangle.
-/
theorem integral_boundary_rect_of_differentiableOn_real (f : ℂ → E) (z w : ℂ)
    (Hd : DifferentiableOn ℝ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hi : IntegrableOn (fun z => I • fderiv ℝ f z 1 - fderiv ℝ f z I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im,
        I • fderiv ℝ f (x + y * I) 1 - fderiv ℝ f (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv ℝ f) z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable at all but countably many points of the corresponding open
rectangle, then its integral over the boundary of the rectangle equals zero. -/
/-
**Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable** 是 
Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : Com
plex -> E) (z w : Complex) (s : Set Complex) (hs : s.Countable) (Hc : Continuous
On f ([[z.re, w.re]] ×Complex [[z.im, w.im]])) (Hd : forall x in Ioo (min z.re w
.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im) \ s, Different
iableAt Complex f x) : (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Rea
l in z.re..w.re, f (x + w.im * I)) + I • (∫ y : Real in z.im..w.im, f (re w + y 
* I)) - I • (∫ y : Real in
参数：f : Complex -> E；z w : Complex；s : Set Complex；hs : s.Countable；Hc : Continuo
usOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]])；Hd : forall x in Ioo (min z.re w
.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im) \ s, Different
iableAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`：integr
al_boundary_rect_of_hasFDerivAt_real_off_countable (f : Complex -> E) (f' : Comp
lex -> Complex ->L[Real] E) (z w : Complex) (s : Set C…
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderiv_eq_smul_deriv`：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -
> F) y = y • deriv f x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0

--- 原说明 ---
**Cauchy-Goursat theorem** for a rectangle: the integral of a complex differenti
able function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuo
us on a closed
rectangle and is complex differentiable at all but countably many points of the 
corresponding open
rectangle, then its integral over the boundary of the rectangle equals zero.
-/
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E) (z w : ℂ)
    (s : Set ℂ) (hs : s.Countable) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 := by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv ℂ f z).restrictScalars ℝ) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars ℝ) ?_).trans ?_ <;>
      simp

/-- **Cauchy-Goursat theorem for a rectangle**: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable on the corresponding open rectangle, then its integral over
the boundary of the rectangle equals zero. -/
/-
**Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn** 是
 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : Co
mplex -> E) (z w : Complex) (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im
, w.im]])) (Hd : DifferentiableOn Complex f (Ioo (min z.re w.re) (max z.re w.re)
 ×Complex Ioo (min z.im w.im) (max z.im w.im))) : (∫ x : Real in z.re..w.re, f (
x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) + I • (∫ y : Real 
in z.im..w.im, f (re w + y * I)) - I • (∫ y : Real in z.im..w.im, f (re z + y * 
I)) = 0
参数：f : Complex -> E；z w : Complex；Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [
[z.im, w.im]])；Hd : DifferentiableOn Complex f (Ioo (min z.re w.re) (max z.re w.
re) ×Complex Ioo (min z.im w.im) (max z.im w.im))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countabl
e`：integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : Comple
x -> E) (z w : Complex) (s : Set Complex) (hs : s.Countable) (H…
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.reProdIm`：IsOpen.reProdIm (hs : IsOpen s) (ht : IsOpen t) : IsOpe
n (s ×Complex t)
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
**Cauchy-Goursat theorem for a rectangle**: the integral of a complex differenti
able function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuo
us on a closed
rectangle and is complex differentiable on the corresponding open rectangle, the
n its integral over
the boundary of the rectangle equals zero.
-/
theorem integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
    fun _x hx => Hd.differentiableAt <| (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is complex differentiable on a
closed rectangle, then its integral over the boundary of the rectangle equals zero. -/
/-
**Complex.integral_boundary_rect_eq_zero_of_differentiableOn** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：integral_boundary_rect_eq_zero_of_differentiableOn (f : Complex -> E) (z w
 : Complex) (H : DifferentiableOn Complex f ([[z.re, w.re]] ×Complex [[z.im, w.i
m]])) : (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re
, f (x + w.im * I)) + I • (∫ y : Real in z.im..w.im, f (re w + y * I)) - I • (∫ 
y : Real in z.im..w.im, f (re z + y * I)) = 0
参数：f : Complex -> E；z w : Complex；H : DifferentiableOn Complex f ([[z.re, w.re]]
 ×Complex [[z.im, w.im]])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiable
On`：integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : Comp
lex -> E) (z w : Complex) (Hc : ContinuousOn f ([[z.re, w.re]] ×…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b

--- 原说明 ---
**Cauchy-Goursat theorem** for a rectangle: the integral of a complex differenti
able function
over the boundary of a rectangle equals zero. More precisely, if `f` is complex 
differentiable on a
closed rectangle, then its integral over the boundary of the rectangle equals ze
ro.
-/
theorem integral_boundary_rect_eq_zero_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn <|
    H.mono <|
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

end rectangle

section annulus
/-!
## Functions on annuli
-/

/-- If `f : ℂ → E` is continuous on the closed annulus `r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`,
and is complex differentiable at all but countably many points of its interior,
then the integrals of `f z / (z - c)` (formally, `(z - c)⁻¹ • f z`)
over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal to each other. -/
/-
**Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off
_countable** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_cou
ntable {c : Complex} {r R : Real} (h0 : 0 < r) (hle : r <= R) {f : Complex -> E}
 {s : Set Complex} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R \ bal
l c r)) (hd : forall z in (ball c R \ closedBall c r) \ s, DifferentiableAt Comp
lex f z) : (∮ z in C(c, R), (z - c)⁻¹ • f z) = ∮ z in C(c, r), (z - c)⁻¹ • f z
参数：h0 : 0 < r；hle : r <= R；hs : s.Countable；hc : ContinuousOn f (closedBall c R 
\ ball c r)；hd : forall z in (ball c R \ closedBall c r) \ s, DifferentiableAt C
omplex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Differentiable.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Complex.differentiable_exp`：differentiable_exp : Differentiable 𝕜 exp
· 使用定理 `Set.Countable.preimage_cexp`：∀ {s : Set ℂ}, s.Countable → (Complex.exp ⁻
¹' s).Countable
· 使用定理 `Set.Countable.preimage`：∀ {α : Type u} {β : Type v} {s : Set β}, s.Count
able → ∀ {f : α → β}, Function.Injective f → (f ⁻¹' s).Countable
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℂ → E` is continuous on the closed annulus `r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R
`,
and is complex differentiable at all but countably many points of its interior,
then the integrals of `f z / (z - c)` (formally, `(z - c)⁻¹ • f z`)
over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal to each other.
-/
theorem circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable {c : ℂ}
    {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = ∮ z in C(c, r), (z - c)⁻¹ • f z := by
  /- We apply the previous lemma to `fun z ↦ f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : ∃ a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : ∃ b, Real.exp b = R := ⟨Real.log R, Real.exp_log (h0.trans_le hle)⟩
  rw [Real.exp_le_exp] at hle
  -- Unfold definition of `circleIntegral` and cancel some terms.
  suffices
    (∫ θ in 0..2 * π, I • f (circleMap c (Real.exp b) θ)) =
      ∫ θ in 0..2 * π, I • f (circleMap c (Real.exp a) θ) by
    simpa only [circleIntegral, add_sub_cancel_left, ofReal_exp, ← exp_add, smul_smul, ←
      div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center (Real.exp_pos _).ne'),
      circleMap_sub_center, deriv_circleMap]
  set R := [[a, b]] ×ℂ [[0, 2 * π]]
  set g : ℂ → ℂ := (c + exp ·)
  have hdg : Differentiable ℂ g := differentiable_exp.const_add _
  replace hs : (g ⁻¹' s).Countable := (hs.preimage (add_right_injective c)).preimage_cexp
  have h_maps : MapsTo g R A := by
    rintro z ⟨h, -⟩; simpa [g, A, dist_eq, norm_exp, hle] using h.symm
  replace hc : ContinuousOn (f ∘ g) R := hc.comp hdg.continuous.continuousOn h_maps
  replace hd : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min 0 (2 * π)) (max 0 (2 * π)) \ g ⁻¹' s,
      DifferentiableAt ℂ (f ∘ g) z := by
    refine fun z hz => (hd (g z) ⟨?_, hz.2⟩).comp z (hdg _)
    simpa [g, dist_eq, norm_exp, hle, and_comm] using hz.1.1
  simpa [g, circleMap, exp_periodic _, sub_eq_zero, ← exp_add] using
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩ _ hs hc hd

/-- **Cauchy-Goursat theorem** for an annulus. If `f : ℂ → E` is continuous on the closed annulus
`r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`, and is complex differentiable at all but countably many points of
its interior, then the integrals of `f` over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal
to each other. -/
/-
**Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable** 是 Mathl
ib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_eq_of_differentiable_on_annulus_off_countable {c : Complex}
 {r R : Real} (h0 : 0 < r) (hle : r <= R) {f : Complex -> E} {s : Set Complex} (
hs : s.Countable) (hc : ContinuousOn f (closedBall c R \ ball c r)) (hd : forall
 z in (ball c R \ closedBall c r) \ s, DifferentiableAt Complex f z) : (∮ z in C
(c, R), f z) = ∮ z in C(c, r), f z
参数：h0 : 0 < r；hle : r <= R；hs : s.Countable；hc : ContinuousOn f (closedBall c R 
\ ball c r)；hd : forall z in (ball c R \ closedBall c r) \ s, DifferentiableAt C
omplex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `circleIntegral.integral_sub_inv_smul_sub_smul`：integral_sub_inv_smul_sub
_smul (f : Complex -> E) (c w : Complex) (R : Real) : (∮ z in C(c, R), (z - w)⁻¹
 • (z - w) • f z) = ∮ z in C(c, R),…
· 使用定理 `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annul
us_off_countable`：circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_ann
ulus_off_countable {c : Complex} {r R : Real} (h0 : 0 < r) (hle : r <= R) {f :…
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `DifferentiableAt.smul`：DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c 
x) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (c • f) x
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x

--- 原说明 ---
**Cauchy-Goursat theorem** for an annulus. If `f : ℂ → E` is continuous on the c
losed annulus
`r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`, and is complex differentiable at all but countab
ly many points of
its interior, then the integrals of `f` over the circles `‖z - c‖ = r` and `‖z -
 c‖ = R` are equal
to each other.
-/
theorem circleIntegral_eq_of_differentiable_on_annulus_off_countable {c : ℂ} {r R : ℝ} (h0 : 0 < r)
    (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z :=
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
        ((continuousOn_id.sub continuousOn_const).smul hc) fun z hz =>
        (differentiableAt_id.sub_const _).smul (hd z hz))
    _ = ∮ z in C(c, r), f z := circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _

end annulus

variable [CompleteSpace E]

section circle
/-!
## Circle integrals
-/

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is continuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many points of the
interior of this disc, and has a limit `y` at the center of the disc, then the integral
$\oint_{‖z-c‖=R} \frac{f(z)}{z-c}\,dz$ is equal to `2πiy`. -/
/-
**Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_
of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_t
endsto {c : Complex} {R : Real} (h0 : 0 < R) {f : Complex -> E} {y : E} {s : Set
 Complex} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R \ {c})) (hd : 
forall z in (ball c R \ {c}) \ s, DifferentiableAt Complex f z) (hy : Tendsto f 
(𝓝[{c}ᶜ] c) (𝓝 y)) : (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : Complex) •
 y
参数：h0 : 0 < R；hs : s.Countable；hc : ContinuousOn f (closedBall c R \ {c})；hd : f
orall z in (ball c R \ {c}) \ s, DifferentiableAt Complex f z；hy : Tendsto f (𝓝[
{c}ᶜ] c) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `Metric.mem_closedBall_self`：mem_closedBall_self (h : 0 <= ε) : x in clos
edBall x ε
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy integral formula** for the value at the center of a disc. If `f` is con
tinuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many
 points of the
interior of this disc, and has a limit `y` at the center of the disc, then the i
ntegral
$\oint_{‖z-c‖=R} \frac{f(z)}{z-c}\,dz$ is equal to `2πiy`.
-/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto {c : ℂ}
    {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ {c}))
    (hd : ∀ z ∈ (ball c R \ {c}) \ s, DifferentiableAt ℂ f z) (hy : Tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : ℂ) • y := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : ∃ δ > (0 : ℝ), ∀ z ∈ closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 Real.two_pi_pos)
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩
  have hsub : closedBall c R \ ball c r ⊆ closedBall c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_ball_self hr0)
  have hsub' : ball c R \ closedBall c r ⊆ ball c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_closedBall_self hr0.le)
  have hzne : ∀ z ∈ sphere c r, z ≠ c := fun z hz =>
    ne_of_mem_of_not_mem hz fun h => hr0.ne' <| dist_self c ▸ Eq.symm h
  /- The integral `∮ z in C(c, r), f z / (z - c)` does not depend on `0 < r ≤ R` and tends to
    `2πIy` as `r → 0`. -/
  calc
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y‖ =
        ‖(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y‖ := by
      congr 2
      · exact circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable hr0
          hrR hs (hc.mono hsub) fun z hz => hd z ⟨hsub' hz.1, hz.2⟩
      · simp [hr0.ne']
    _ = ‖∮ z in C(c, r), (z - c)⁻¹ • (f z - y)‖ := by
      simp only [smul_sub]
      have hc' : ContinuousOn (fun z => (z - c)⁻¹) (sphere c r) :=
        (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 <| hzne _ hz
      rw [circleIntegral.integral_sub] <;> refine (hc'.smul ?_).circleIntegrable hr0.le
      · exact hc.mono <| subset_inter
          (sphere_subset_closedBall.trans <| closedBall_subset_closedBall hrR) hzne
      · exact continuousOn_const
    _ ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => ?_
      specialize hzne z hz
      rw [mem_sphere, dist_eq_norm] at hz
      rw [norm_smul, norm_inv, hz, ← dist_eq_norm]
      refine mul_le_mul_of_nonneg_left (hδ _ ⟨?_, hzne⟩).le (inv_nonneg.2 hr0.le)
      rwa [mem_closedBall_iff_norm, hz]
    _ = ε := by field

/--
**Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$ is equal to
`2πi • f c`.
-/
/-
**Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable*
* 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R :
 Real} (h0 : 0 < R) {f : Complex -> E} {c : Complex} {s : Set Complex} (hs : s.C
ountable) (hc : ContinuousOn f (closedBall c R)) (hd : forall z in ball c R \ s,
 DifferentiableAt Complex f z) : (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I)
 • f c
参数：h0 : 0 < R；hs : s.Countable；hc : ContinuousOn f (closedBall c R)；hd : forall 
z in ball c R \ s, DifferentiableAt Complex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_coun
table_of_tendsto`：circleIntegral_sub_center_inv_smul_of_differentiable_on_off_co
untable_of_tendsto {c : Complex} {R : Real} (h0 : 0 < R) {f : Complex -> E} {y…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x

--- 原说明 ---
**Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E
` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all b
ut countably many
points of its interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$
 is equal to
`2πi • f c`.
-/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
    {f : ℂ → E} {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I) • f c :=
  circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono sdiff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt

omit [CompleteSpace E] in
/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable at all but countably many points of its interior,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
/-
**Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable** 是 Mathlib 
中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_eq_zero_of_differentiable_on_off_countable {R : Real} (h0 :
 0 <= R) {f : Complex -> E} {c : Complex} {s : Set Complex} (hs : s.Countable) (
hc : ContinuousOn f (closedBall c R)) (hd : forall z in ball c R \ s, Differenti
ableAt Complex f z) : (∮ z in C(c, R), f z) = 0
参数：h0 : 0 <= R；hs : s.Countable；hc : ContinuousOn f (closedBall c R)；hd : forall
 z in ball c R \ s, DifferentiableAt Complex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `circleIntegral.integral_radius_zero`：integral_radius_zero (f : Complex -
> E) (c : Complex) : (∮ z in C(c, 0), f z) = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `circleIntegral.integral_sub_inv_smul_sub_smul`：integral_sub_inv_smul_sub
_smul (f : Complex -> E) (c w : Complex) (R : Real) : (∮ z in C(c, R), (z - w)⁻¹
 • (z - w) • f z) = ∮ z in C(c, R),…
· 使用定理 `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_coun
table`：circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R 
: Real} (h0 : 0 < R) {f : Complex -> E} {c : Complex} {s : Set Comp…
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `DifferentiableAt.smul`：DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c 
x) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (c • f) x
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed 
disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable at all but countably many poin
ts of its interior,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero.
-/
theorem circleIntegral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
    {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0 := by
  wlog hE : CompleteSpace E generalizing
  · simp [circleIntegral, intervalIntegral, integral, hE]
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = (2 * ↑π * I : ℂ) • (c - c) • f c :=
      (circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
        ((continuousOn_id.sub continuousOn_const).smul hc) fun z hz =>
        (differentiableAt_id.sub_const _).smul (hd z hz))
    _ = 0 := by rw [sub_self, zero_smul, smul_zero]

omit [CompleteSpace E] in
/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable on the open disk,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
/-
**Complex._root_.DiffContOnCl.circleIntegral_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed 
disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable on the open disk,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero.
-/
theorem _root_.DiffContOnCl.circleIntegral_eq_zero {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
    {c : ℂ} (hc : DiffContOnCl ℂ f (ball c R)) : ∮ z in C(c, R), f z = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable h0 countable_empty
    hc.continuousOn_ball fun _z hz ↦ hc.differentiableAt isOpen_ball hz.1

/-- An auxiliary lemma for
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`. This lemma assumes
`w ∉ s` while the main lemma drops this assumption. -/
/-
**Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux** 是
 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : Re
al} {c w : Complex} {f : Complex -> E} {s : Set Complex} (hs : s.Countable) (hw 
: w in ball c R \ s) (hc : ContinuousOn f (closedBall c R)) (hd : forall x in ba
ll c R \ s, DifferentiableAt Complex f x) : (∮ z in C(c, R), (z - w)⁻¹ • f z) = 
(2 * π * I : Complex) • f w
参数：hs : s.Countable；hw : w in ball c R \ s；hc : ContinuousOn f (closedBall c R)；
hd : forall x in ball c R \ s, DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Countable.insert`：∀ {α : Type u} {s : Set α} (a : α), s.Countable → 
(insert a s).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_dslope`：continuousOn_dslope (h : s in 𝓝 a) : ContinuousOn (
dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a
· 使用定理 `Metric.closedBall_mem_nhds_of_mem`：closedBall_mem_nhds_of_mem {x c : α} 
{ε : Real} (h : x in ball c ε) : closedBall c ε in 𝓝 x
· 使用定理 `differentiableAt_dslope_of_ne`：differentiableAt_dslope_of_ne (h : b != a
) : DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`：circl
eIntegral_eq_zero_of_differentiable_on_off_countable {R : Real} (h0 : 0 <= R) {f
 : Complex -> E} {c : Complex} {s : Set Complex} (hs : …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary lemma for
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`. This l
emma assumes
`w ∉ s` while the main lemma drops this assumption.
-/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ}
    {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ s)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : ℂ → E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : ∀ z ∈ ball (c : ℂ) R \ insert w s, DifferentiableAt ℂ F z := fun z hz =>
    (differentiableAt_dslope_of_ne (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (sdiff_subset_sdiff_right (subset_insert _ _) hz))
  have HI := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF
  have hne : ∀ z ∈ sphere c R, z ≠ w := fun z hz => ne_of_mem_of_not_mem hz (ne_of_lt hw.1)
  have hFeq : EqOn F (fun z => (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R) := fun z hz ↦
    calc
      F z = (z - w)⁻¹ • (f z - f w) := update_of_ne (hne z hz) ..
      _ = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w := smul_sub _ _ _
  have hc' : ContinuousOn (fun z => (z - w)⁻¹) (sphere c R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 <| hne z hz
  rw [← circleIntegral.integral_sub_inv_of_mem_ball hw.1, ← circleIntegral.integral_smul_const, ←
    sub_eq_zero, ← circleIntegral.integral_sub, ← circleIntegral.integral_congr hR.le hFeq, HI]
  exacts [(hc'.smul (hc.mono sphere_subset_closedBall)).circleIntegrable hR.le,
    (hc'.smul continuousOn_const).circleIntegrable hR.le]

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
/-
**Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off
_countable** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_cou
ntable {R : Real} {c w : Complex} {f : Complex -> E} {s : Set Complex} (hs : s.C
ountable) (hw : w in ball c R) (hc : ContinuousOn f (closedBall c R)) (hd : fora
ll x in ball c R \ s, DifferentiableAt Complex f x) : ((2 * π * I : Complex)⁻¹ •
 ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w
参数：hs : s.Countable；hw : w in ball c R；hc : ContinuousOn f (closedBall c R)；hd :
 forall x in ball c R \ s, DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Set.sdiff_nonempty`：sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s
 subseteq t
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.Countable.preimage`：∀ {α : Type u} {β : Type v} {s : Set β}, s.Count
able → ∀ {f : α → β}, Function.Injective f → (f ⁻¹' s).Countable
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Complex.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : R
eal -> Complex)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of ra
dius `R` and is
complex differentiable at all but countably many points of its interior, then fo
r any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ}
    {c w : ℂ} {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w ∈ closure (ball c R \ s) by
    lift R to ℝ≥0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg) hR
      refine this.continuousOn.continuousAt (Metric.isOpen_eball.mem_nhds ?_)
      rwa [Metric.eball_coe]
    have B : ContinuousAt f w := hc.continuousAt (closedBall_mem_nhds_of_mem hw)
    refine tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono ?_)
    intro z hz
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd,
      inv_smul_smul₀]
    simp [Real.pi_ne_zero, I_ne_zero]
  refine mem_closure_iff_nhds.2 fun t ht => ?_
  -- TODO: generalize to any vector space over `ℝ`
  set g : ℝ → ℂ := fun x => w + ofReal x
  have : Tendsto g (𝓝 0) (𝓝 w) := Continuous.tendsto' (by fun_prop) 0 w (add_zero _)
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this <| inter_mem ht <| isOpen_ball.mem_nhds hw) with
    ⟨l, u, hlu₀, hlu_sub⟩
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).Nonempty := by
    refine sdiff_nonempty.2 fun hsub => ?_
    have : (Ioo l u).Countable :=
      (hs.preimage ((add_right_injective w).comp ofReal_injective)).mono hsub
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this
    exact this.not_gt Cardinal.aleph0_lt_continuum
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
/-
**Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable** 是 Mat
hlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : Real} 
{c w : Complex} {f : Complex -> E} {s : Set Complex} (hs : s.Countable) (hw : w 
in ball c R) (hc : ContinuousOn f (closedBall c R)) (hd : forall x in ball c R \
 s, DifferentiableAt Complex f x) : (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π *
 I : Complex) • f w
参数：hs : s.Countable；hw : w in ball c R；hc : ContinuousOn f (closedBall c R)；hd :
 forall x in ball c R \ s, DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_
on_off_countable`：two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiabl
e_on_off_countable {R : Real} {c w : Complex} {f : Complex -> E} {s : Set Comp…
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of ra
dius `R` and is
complex differentiable at all but countably many points of its interior, then fo
r any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd, smul_inv_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
/-
**Complex._root_.DiffContOnCl.circleIntegral_sub_inv_smul** 是 Mathlib 中的一个定理，位于命
名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open
 disc and is
continuous on its closure, then for any `w` in this open ball we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
theorem _root_.DiffContOnCl.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (h : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$. -/
/-
**Complex._root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul** 是 
Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open
 disc and is
continuous on its closure, then for any `w` in this open ball we have
$\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
theorem _root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ}
    {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [sdiff_empty] using fun z hz => hf.differentiableAt isOpen_ball hz

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a closed disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
/-
**Complex._root_.DifferentiableOn.circleIntegral_sub_inv_smul** 是 Mathlib 中的一个定理
，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a close
d disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz
=2πif(w)$.
-/
theorem _root_.DifferentiableOn.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw

/-- **Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
/-
**Complex.circleIntegral_div_sub_of_differentiable_on_off_countable** 是 Mathlib 
中的一个定理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_div_sub_of_differentiable_on_off_countable {R : Real} {c w 
: Complex} {s : Set Complex} (hs : s.Countable) (hw : w in ball c R) {f : Comple
x -> Complex} (hc : ContinuousOn f (closedBall c R)) (hd : forall z in ball c R 
\ s, DifferentiableAt Complex f z) : (∮ z in C(c, R), f z / (z - w)) = 2 * π * I
 * f w
参数：hs : s.Countable；hw : w in ball c R；hc : ContinuousOn f (closedBall c R)；hd :
 forall z in ball c R \ s, DifferentiableAt Complex f z。
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
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`：
circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : Real} {c w :
 Complex} {f : Complex -> E} {s : Set Complex} (hs : s.Count…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
**Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of ra
dius `R` and is
complex differentiable at all but countably many points of its interior, then fo
r any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
theorem circleIntegral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ ball c R) {f : ℂ → ℂ} (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w := by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

end circle

section analyticity
/-!
## Applications to analyticity
-/

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is differentiable at all
but countably many points of the corresponding open ball, then it is analytic on the open ball with
coefficients of the power series given by Cauchy integral formulas. -/
/-
**Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable** 是 Mathlib 中的一个
定理，位于命名空间 `Complex`。
形式化陈述：hasFPowerSeriesOnBall_of_differentiable_off_countable {R : Real>=0} {c : C
omplex} {f : Complex -> E} {s : Set Complex} (hs : s.Countable) (hc : Continuous
On f (closedBall c R)) (hd : forall z in ball c R \ s, DifferentiableAt Complex 
f z) (hR : 0 < R) : HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R where 
r_le
参数：hs : s.Countable；hc : ContinuousOn f (closedBall c R)；hd : forall z in ball c
 R \ s, DifferentiableAt Complex f z；hR : 0 < R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_radius_cauchyPowerSeries`：le_radius_cauchyPowerSeries (f : Complex ->
 E) (c : Complex) (R : Real>=0) : ↑R <= (cauchyPowerSeries f c R).radius
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_
on_off_countable`：two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiabl
e_on_off_countable {R : Real} {c w : Complex} {f : Complex -> E} {s : Set Comp…
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `hasFPowerSeriesOn_cauchy_integral`：hasFPowerSeriesOn_cauchy_integral {f 
: Complex -> E} {c : Complex} {R : Real>=0} (hf : CircleIntegrable f c R) (hR : 
0 < R) : HasFPowerSerie…
· 使用定理 `ContinuousOn.circleIntegrable`：ContinuousOn.circleIntegrable {f : Comple
x -> E} {c : Complex} {R : Real} (hR : 0 <= R) (hf : ContinuousOn f (sphere c R)
) : CircleIntegrabl…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε

--- 原说明 ---
If `f : ℂ → E` is continuous on a closed ball of positive radius and is differen
tiable at all
but countably many points of the corresponding open ball, then it is analytic on
 the open ball with
coefficients of the power series given by Cauchy integral formulas.
-/
theorem hasFPowerSeriesOnBall_of_differentiable_off_countable {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R where
  r_le := le_radius_cauchyPowerSeries _ _ _
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : c + w ∈ ball c R := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
        NNReal.coe_lt_coe, enorm_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      hs hw' hc hd]
    exact (hasFPowerSeriesOn_cauchy_integral
      ((hc.mono sphere_subset_closedBall).circleIntegrable R.2) hR).hasSum hw

/-- If `f : ℂ → E` is complex differentiable on an open disc of positive radius and is continuous
on its closure, then it is analytic on the open disc with coefficients of the power series given by
Cauchy integral formulas. -/
/-
**Complex._root_.DiffContOnCl.hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ℂ → E` is complex differentiable on an open disc of positive radius and 
is continuous
on its closure, then it is analytic on the open disc with coefficients of the po
wer series given by
Cauchy integral formulas.
-/
theorem _root_.DiffContOnCl.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR

/-- If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, then it is
analytic on the corresponding open disc, and the coefficients of the power series are given by
Cauchy integral formulas. See also
`Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable` for a version of this lemma with
weaker assumptions. -/
/-
**Complex._root_.DifferentiableOn.hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空
间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, th
en it is
analytic on the corresponding open disc, and the coefficients of the power serie
s are given by
Cauchy integral formulas. See also
`Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable` for a version of
 this lemma with
weaker assumptions.
-/
protected theorem _root_.DifferentiableOn.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR

/-- If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`). -/
/-
**Complex._root_.DifferentiableOn.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at
 any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`).
-/
protected theorem _root_.DifferentiableOn.analyticAt {s : Set ℂ} {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt
/-
**Complex._root_.DifferentiableOn.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableOn.analyticOnNhd {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s := fun _z hz => hd.analyticAt (hs.mem_nhds hz)
/-
**Complex._root_.DifferentiableOn.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableOn.analyticOn {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOn ℂ f s :=
  (hd.analyticOnNhd hs).analyticOn

/-- If `f : ℂ → E` is complex differentiable on some open set `s`, then it is continuously
differentiable on `s`. -/
/-
**Complex._root_.DifferentiableOn.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ℂ → E` is complex differentiable on some open set `s`, then it is contin
uously
differentiable on `s`.
-/
protected theorem _root_.DifferentiableOn.contDiffOn {s : Set ℂ} {f : ℂ → E} {n : WithTop ℕ∞}
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) : ContDiffOn ℂ n f s :=
  (hd.analyticOnNhd hs).contDiffOn_of_completeSpace
/-
**Complex._root_.DifferentiableOn.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableOn.deriv {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : DifferentiableOn ℂ (deriv f) s :=
  (hd.analyticOnNhd hs).deriv.differentiableOn

/-- A complex differentiable function `f : ℂ → E` is analytic at every point. -/
/-
**Complex._root_.Differentiable.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complex differentiable function `f : ℂ → E` is analytic at every point.
-/
protected theorem _root_.Differentiable.analyticAt {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  hf.differentiableOn.analyticAt univ_mem

/-- A complex differentiable function `f : ℂ → E` is continuously differentiable at every point. -/
/-
**Complex._root_.Differentiable.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complex differentiable function `f : ℂ → E` is continuously differentiable at 
every point.
-/
protected theorem _root_.Differentiable.contDiff
    {f : ℂ → E} (hf : Differentiable ℂ f) {n : WithTop ℕ∞} :
    ContDiff ℂ n f :=
  contDiff_iff_contDiffAt.mpr fun z ↦ (hf.analyticAt z).contDiffAt

@[fun_prop]
/-
**Complex._root_.Differentiable.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Differentiable.deriv {f : ℂ → E} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  hf.contDiff.differentiable_deriv_two

/-- When `f : ℂ → E` is differentiable, the `cauchyPowerSeries f z R` represents `f` as a power
series centered at `z` in the entirety of `ℂ`, regardless of `R : ℝ≥0`, with `0 < R`. -/
/-
**Complex._root_.Differentiable.hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f : ℂ → E` is differentiable, the `cauchyPowerSeries f z R` represents `f`
 as a power
series centered at `z` in the entirety of `ℂ`, regardless of `R : ℝ≥0`, with `0 
< R`.
-/
protected theorem _root_.Differentiable.hasFPowerSeriesOnBall {f : ℂ → E} (h : Differentiable ℂ f)
    (z : ℂ) {R : ℝ≥0} (hR : 0 < R) : HasFPowerSeriesOnBall f (cauchyPowerSeries f z R) z ∞ :=
  (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩

/-- On an open set, `f : ℂ → E` is analytic iff it is differentiable -/
/-
**Complex.analyticOnNhd_iff_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：analyticOnNhd_iff_differentiableOn {f : Complex -> E} {s : Set Complex} (o
 : IsOpen s) : AnalyticOnNhd Complex f s ↔ DifferentiableOn Complex f s
参数：o : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.differentiableOn`：AnalyticOnNhd.differentiableOn (h : Anal
yticOnNhd 𝕜 f s) : DifferentiableOn 𝕜 f s
· 使用定理 `DifferentiableOn.analyticAt`：∀ {E : Type u} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}   {z : ℂ}
, DifferentiableO…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
On an open set, `f : ℂ → E` is analytic iff it is differentiable
-/
theorem analyticOnNhd_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun d _ zs ↦ d.analyticAt (o.mem_nhds zs)⟩

/-- On an open set, `f : ℂ → E` is analytic iff it is differentiable -/
/-
**Complex.analyticOn_iff_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOn_iff_differentiableOn {f : Complex -> E} {s : Set Complex} (o : 
IsOpen s) : AnalyticOn Complex f s ↔ DifferentiableOn Complex f s
参数：o : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsOpen.analyticOn_iff_analyticOnNhd`：IsOpen.analyticOn_iff_analyticOnNhd
 {f : E -> F} {s : Set E} (hs : IsOpen s) : AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f
 s
· 使用定理 `Complex.analyticOnNhd_iff_differentiableOn`：analyticOnNhd_iff_differenti
ableOn {f : Complex -> E} {s : Set Complex} (o : IsOpen s) : AnalyticOnNhd Compl
ex f s ↔ DifferentiableOn Comple…

--- 原说明 ---
On an open set, `f : ℂ → E` is analytic iff it is differentiable
-/
theorem analyticOn_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOn ℂ f s ↔ DifferentiableOn ℂ f s := by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o

/-- `f : ℂ → E` is entire iff it's differentiable -/
/-
**Complex.analyticOnNhd_univ_iff_differentiable** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex`。
形式化陈述：analyticOnNhd_univ_iff_differentiable {f : Complex -> E} : AnalyticOnNhd C
omplex f univ ↔ Differentiable Complex f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.analyticOnNhd_iff_differentiableOn`：analyticOnNhd_iff_differenti
ableOn {f : Complex -> E} {s : Set Complex} (o : IsOpen s) : AnalyticOnNhd Compl
ex f s ↔ DifferentiableOn Comple…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
`f : ℂ → E` is entire iff it's differentiable
-/
theorem analyticOnNhd_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOnNhd ℂ f univ ↔ Differentiable ℂ f := by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ
/-
**Complex.analyticOn_univ_iff_differentiable** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：analyticOn_univ_iff_differentiable {f : Complex -> E} : AnalyticOn Complex
 f univ ↔ Differentiable Complex f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `analyticOn_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 …
· 使用定理 `Complex.analyticOnNhd_univ_iff_differentiable`：analyticOnNhd_univ_iff_di
fferentiable {f : Complex -> E} : AnalyticOnNhd Complex f univ ↔ Differentiable 
Complex f
-/
theorem analyticOn_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOn ℂ f univ ↔ Differentiable ℂ f := by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable

/-- `f : ℂ → E` is analytic at `z` iff it's differentiable near `z` -/
/-
**Complex.analyticAt_iff_eventually_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
形式化陈述：analyticAt_iff_eventually_differentiableAt {f : Complex -> E} {c : Complex
} : AnalyticAt Complex f c ↔ forallᶠ z in 𝓝 c, DifferentiableAt Complex f z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
`f : ℂ → E` is analytic at `z` iff it's differentiable near `z`
-/
theorem analyticAt_iff_eventually_differentiableAt {f : ℂ → E} {c : ℂ} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt]
    apply AnalyticAt.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd ℂ f s := by
      refine DifferentiableOn.analyticOnNhd ?_ o
      intro z m
      exact (d z m).differentiableWithinAt
    exact h _ m

end analyticity

section derivatives
/-!
## Circle integrals for higher derivatives

TODO: add a version for `w ∈ Metric.ball c R`.
-/

variable {R : ℝ} {f : ℂ → E} {c : ℂ} {s : Set ℂ}

/-- **Cauchy integral formula for derivatives**, assuming `f` is continuous on a closed ball and
differentiable on its interior away from a countable set. -/
/-
**Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_co
untable** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_counta
ble (h0 : 0 < R) (n : Nat) (hs : s.Countable) (hc : ContinuousOn f (closedBall c
 R)) (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) : ∮ z in C(c,
 R), (1 / (z - c) ^ (n + 1)) • f z = (2 * π * I / n.factorial) • iteratedDeriv n
 f c
参数：h0 : 0 < R；n : Nat；hs : s.Countable；hc : ContinuousOn f (closedBall c R)；hd :
 forall z in ball c R \ s, DifferentiableAt Complex f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HasFPowerSeriesOnBall.factorial_smul`：factorial_smul (n : Nat) : n ! • p
 n (fun _ => y) = iteratedFDeriv 𝕜 n f x (fun _ => y)
· 使用定理 `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`：hasFPower
SeriesOnBall_of_differentiable_off_countable {R : Real>=0} {c : Complex} {f : Co
mplex -> E} {s : Set Complex} (hs : s.Countable) (h…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`：iteratedFDeriv_apply_eq_
iteratedDeriv_mul_prod {m : Fin n -> 𝕜} : (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜)
 -> F) m = (∏ i, m i) • iteratedDeri…
· 使用定理 `cauchyPowerSeries_apply`：cauchyPowerSeries_apply (f : Complex -> E) (c :
 Complex) (R : Real) (n : Nat) (w : Complex) : (cauchyPowerSeries f c R n fun _ 
=> w) = (2 * …
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Cauchy integral formula for derivatives**, assuming `f` is continuous on a clo
sed ball and
differentiable on its interior away from a countable set.
-/
lemma circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (h0 : 0 < R) (n : ℕ) (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c := by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := .mk R h0.le) hs hc hd h0
      |>.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at this
  rw [← this, cauchyPowerSeries_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, ← mul_smul,
    div_mul_cancel₀ _ (mod_cast n.factorial_ne_zero), mul_inv_cancel₀ two_pi_I_ne_zero]
  simp [← mul_smul, pow_succ, mul_comm]

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is continuous on a
closed ball and differentiable on its interior away from a countable set. -/
/-
**Complex.differentiable_on_off_countable_deriv_eq_smul_circleIntegral** 是 Mathl
ib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：differentiable_on_off_countable_deriv_eq_smul_circleIntegral (h0 : 0 < R) 
(hs : s.Countable) (hc : ContinuousOn f (closedBall c R)) (hd : forall z in ball
 c R \ s, DifferentiableAt Complex f z) : ∮ z in C(c, R), (1 / (z - c) ^ 2) • f 
z = (2 * π * I) • deriv f c
参数：h0 : 0 < R；hs : s.Countable；hc : ContinuousOn f (closedBall c R)；hd : forall 
z in ball c R \ s, DifferentiableAt Complex f z。
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用引理 `Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_
off_countable`：circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_o
ff_countable (h0 : 0 < R) (n : Nat) (hs : s.Countable) (hc : ContinuousOn f…

--- 原说明 ---
**Cauchy integral formula for the first order derivative**, assuming `f` is cont
inuous on a
closed ball and differentiable on its interior away from a countable set.
-/
lemma differentiable_on_off_countable_deriv_eq_smul_circleIntegral
    (h0 : 0 < R) (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    h0 1 hs hc hd

/-- **Cauchy integral formula for derivatives**, assuming `f` is continuous on a closed ball and
differentiable on its interior. -/
/-
**Complex._root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul** 是 Mat
hlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula for derivatives**, assuming `f` is continuous on a clo
sed ball and
differentiable on its interior.
-/
lemma _root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
    (h0 : 0 < R) (n : ℕ) (hc : DiffContOnCl ℂ f (ball c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx ↦ hc.differentiableAt isOpen_ball hx.1

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is continuous on a
closed ball and differentiable on its interior. -/
/-
**Complex._root_.DiffContOnCl.deriv_eq_smul_circleIntegral** 是 Mathlib 中的一个引理，位于
命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula for the first order derivative**, assuming `f` is cont
inuous on a
closed ball and differentiable on its interior.
-/
lemma _root_.DiffContOnCl.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DiffContOnCl ℂ f (ball c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

/-- **Cauchy integral formula for derivatives**, assuming `f` is differentiable on a closed ball. -/
/-
**Complex._root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul** 是
 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula for derivatives**, assuming `f` is differentiable on a
 closed ball.
-/
lemma _root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul (h0 : 0 < R) (n : ℕ)
    (hc : DifferentiableOn ℂ f (closedBall c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  (hc.mono closure_ball_subset_closedBall).diffContOnCl
    |>.circleIntegral_one_div_sub_center_pow_smul h0 n

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is differentiable on
a closed ball. -/
/-
**Complex._root_.DifferentiableOn.deriv_eq_smul_circleIntegral** 是 Mathlib 中的一个引
理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cauchy integral formula for the first order derivative**, assuming `f` is diff
erentiable on
a closed ball.
-/
lemma _root_.DifferentiableOn.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DifferentiableOn ℂ f (closedBall c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

end derivatives

end Complex

