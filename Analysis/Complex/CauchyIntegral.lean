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

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Complex E]

namespace Complex

section rectangle
/-!
## Functions on rectangles
-/

/--
theorem `integral_boundary_rect_of_hasFDerivAt_real_off_countable` / 定理 `integral_boundary_rect_of_hasFDerivAt_real_off_countable`

English:
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable
  statement: (f : Complex -> E) (f' : Complex -> Complex ->L[Real] E)
  proof: by
  set e : (Real × Real) ≃L[Real] Complex := equivRealProdCLM.symm
  have he : forall x y : Real, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : Real × Real -> E := f ∘ e
  set F' : Re

中文:
定理 integral_boundary_rect_of_hasFDerivAt_real_off_countable
  结论: (f : 复形 -> E) (f' : 复形 -> 复形 ->L[实数] E)
  证明: by
  set e : (Real × Real) ≃L[Real] Complex := equivRealProdCLM.symm
  have he : forall x y : Real, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : Real × Real -> E := f ∘ e
  set F' : Re

Depends on / 依赖: equivRealProdCLM, equivRealProdCLM.symm, mk_eq_add_mul_I
-/
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : Complex -> E) (f' : Complex -> Complex ->L[Real] E)
    (z w : Complex) (s : Set Complex) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
    (Hd : forall x in Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im) \ s,
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×Complex [[z.im, w.im]])) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : Real in z.im..w.im, f (re z + y * I) =
      ∫ x : Real in z.re..w.re, ∫ y : Real in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I := by
  set e : (Real × Real) ≃L[Real] Complex := equivRealProdCLM.symm
  have he : forall x y : Real, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : Real × Real -> E := f ∘ e
  set F' : Real × Real -> Real × Real ->L[Real] E := fun p => (f' (e p)).comp (e : Real × Real ->L[Real] Complex)
  have hF' : forall p : Real × Real, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I) := by
    rintro ⟨x, y⟩
    simp only [F', neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, he₁, he₂, neg_add_eq_sub, neg_sub]
  set R : Set (Real × Real) := [[z.re, w.re]] ×ˢ [[w.im, z.im]]
  set t : Set (Real × Real) := e ⁻¹' s
  rw [uIcc_comm z.im] at Hc Hi; rw [min_comm z.im, max_comm z.im] at Hd
  have hR : e ⁻¹' ([[z.re, w.re]] ×Complex [[w.im, z.im]]) = R := rfl
  have htc : ContinuousOn F R := Hc.comp e.continuousOn hR.ge
  have htd :
    forall p in Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t,
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

/--
theorem `integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real` / 定理 `integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real`

English:
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real
  statement: (f : Complex -> E) (f' : Complex -> Complex ->L[Real] E)
  proof: integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi

中文:
定理 integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real
  结论: (f : 复形 -> E) (f' : 复形 -> 复形 ->L[实数] E)
  证明: integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi

Depends on / 依赖: countable_empty, integral_boundary_rect_of_hasFDerivAt_real_off_countable
-/
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real (f : Complex -> E) (f' : Complex -> Complex ->L[Real] E)
    (z w : Complex) (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
    (Hd : forall x in Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im),
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×Complex [[z.im, w.im]])) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (re z + y * I)) =
      ∫ x : Real in z.re..w.re, ∫ y : Real in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi

/--
theorem `integral_boundary_rect_of_differentiableOn_real` / 定理 `integral_boundary_rect_of_differentiableOn_real`

English:
theorem integral_boundary_rect_of_differentiableOn_real
  statement: (f : Complex -> E) (z w : Complex)
  proof: integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv Real f) z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi

中文:
定理 integral_boundary_rect_of_differentiableOn_real
  结论: (f : 复形 -> E) (z w : 复形)
  证明: integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv Real f) z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi

Depends on / 依赖: Hd.continuousOn, Hd.hasFDerivAt, continuousOn, countable_empty, fderiv, hasFDerivAt, integral_boundary_rect_of_hasFDerivAt_real_off_countable, interior_Icc, interior_reProdIm, mem_interior_iff_mem_nhds
-/
theorem integral_boundary_rect_of_differentiableOn_real (f : Complex -> E) (z w : Complex)
    (Hd : DifferentiableOn Real f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
    (Hi : IntegrableOn (fun z => I • fderiv Real f z 1 - fderiv Real f z I)
      ([[z.re, w.re]] ×Complex [[z.im, w.im]])) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (re z + y * I)) =
      ∫ x : Real in z.re..w.re, ∫ y : Real in z.im..w.im,
        I • fderiv Real f (x + y * I) 1 - fderiv Real f (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv Real f) z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi

/--
theorem `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` / 定理 `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`

English:
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
  statement: (f : Complex -> E) (z w : Complex)
  proof: by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv Complex f z).restrictScalars Real) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars Real) ?_).trans ?_ <;>
      simp

中文:
定理 integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
  结论: (f : 复形 -> E) (z w : 复形)
  证明: by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv Complex f z).restrictScalars Real) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars Real) ?_).trans ?_ <;>
      simp

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt.restrictScalars, integral_boundary_rect_of_hasFDerivAt_real_off_countable, restrictScalars
-/
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : Complex -> E) (z w : Complex)
    (s : Set Complex) (hs : s.Countable) (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
    (Hd : forall x in Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt Complex f x) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (re z + y * I)) = 0 := by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv Complex f z).restrictScalars Real) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars Real) ?_).trans ?_ <;>
      simp

/--
theorem `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` / 定理 `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`

English:
theorem integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  statement: (f : Complex -> E) (z w : Complex)
  proof: integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
fun _x hx => Hd.differentiableAt (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1

中文:
定理 integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  结论: (f : 复形 -> E) (z w : 复形)
  证明: integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
fun _x hx => Hd.differentiableAt (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1

Depends on / 依赖: Hd.differentiableAt, countable_empty, differentiableAt, integral_boundary_rect_eq_zero_of_differentiable_on_off_countable, isOpen_Ioo, isOpen_Ioo.reProdIm, mem_nhds, reProdIm
-/
theorem integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : Complex -> E) (z w : Complex)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×Complex [[z.im, w.im]]))
    (Hd : DifferentiableOn Complex f
      (Ioo (min z.re w.re) (max z.re w.re) ×Complex Ioo (min z.im w.im) (max z.im w.im))) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
fun _x hx => Hd.differentiableAt (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1

/--
theorem `integral_boundary_rect_eq_zero_of_differentiableOn` / 定理 `integral_boundary_rect_eq_zero_of_differentiableOn`

English:
theorem integral_boundary_rect_eq_zero_of_differentiableOn
  statement: (f : Complex -> E) (z w : Complex)
  proof: integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn
H.mono
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

中文:
定理 integral_boundary_rect_eq_zero_of_differentiableOn
  结论: (f : 复形 -> E) (z w : 复形)
  证明: integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn
H.mono
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

Depends on / 依赖: H.continuousOn, H.mono, Ioo_subset_Icc_self, continuousOn, integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn, inter_subset_inter, preimage_mono
-/
theorem integral_boundary_rect_eq_zero_of_differentiableOn (f : Complex -> E) (z w : Complex)
    (H : DifferentiableOn Complex f ([[z.re, w.re]] ×Complex [[z.im, w.im]])) :
    (∫ x : Real in z.re..w.re, f (x + z.im * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (re z + y * I)) = 0 :=
integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn
H.mono
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

end rectangle

section annulus
/-!
## Functions on annuli
-/

/--
theorem `circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable` / 定理 `circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`

English:
theorem circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
  statement: {c : Complex}
  proof: by
  /- We apply the previous lemma to `fun z ↦ f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : exists a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : exists b, Real.exp b = R := ⟨Real.log R, Real.e

中文:
定理 circle整数egral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
  结论: {c : 复形}
  证明: by
  /- We apply the previous lemma to `fun z ↦ f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : exists a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : exists b, Real.exp b = R := ⟨Real.log R, Real.e
-/
theorem circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable {c : Complex}
    {r R : Real} (h0 : 0 < r) (hle : r <= R) {f : Complex -> E} {s : Set Complex} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : forall z in (ball c R \ closedBall c r) \ s, DifferentiableAt Complex f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = ∮ z in C(c, r), (z - c)⁻¹ • f z := by
  /- We apply the previous lemma to `fun z ↦ f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : exists a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : exists b, Real.exp b = R := ⟨Real.log R, Real.exp_log (h0.trans_le hle)⟩
  rw [Real.exp_le_exp] at hle
  -- Unfold definition of `circleIntegral` and cancel some terms.
  suffices
    (∫ θ in 0..2 * π, I • f (circleMap c (Real.exp b) θ)) =
      ∫ θ in 0..2 * π, I • f (circleMap c (Real.exp a) θ) by
    simpa only [circleIntegral, add_sub_cancel_left, ofReal_exp, ← exp_add, smul_smul, ←
      div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center (Real.exp_pos _).ne'),
      circleMap_sub_center, deriv_circleMap]
  set R := [[a, b]] ×Complex [[0, 2 * π]]
  set g : Complex -> Complex := (c + exp ·)
  have hdg : Differentiable Complex g := differentiable_exp.const_add _
  replace hs : (g ⁻¹' s).Countable := (hs.preimage (add_right_injective c)).preimage_cexp
  have h_maps : MapsTo g R A := by
    rintro z ⟨h, -⟩; simpa [g, A, dist_eq, norm_exp, hle] using h.symm
  replace hc : ContinuousOn (f ∘ g) R := hc.comp hdg.continuous.continuousOn h_maps
  replace hd : forall z in Ioo (min a b) (max a b) ×Complex Ioo (min 0 (2 * π)) (max 0 (2 * π)) \ g ⁻¹' s,
      DifferentiableAt Complex (f ∘ g) z := by
    refine fun z hz => (hd (g z) ⟨?_, hz.2⟩).comp z (hdg _)
    simpa [g, dist_eq, norm_exp, hle, and_comm] using hz.1.1
  simpa [g, circleMap, exp_periodic _, sub_eq_zero, ← exp_add] using
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩ _ hs hc hd

/--
theorem `circleIntegral_eq_of_differentiable_on_annulus_off_countable` / 定理 `circleIntegral_eq_of_differentiable_on_annulus_off_countable`

English:
theorem circleIntegral_eq_of_differentiable_on_annulus_off_countable
  statement: {c : Complex} {r R : Real} (h0 : 0 < r)
  proof: calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
    

中文:
定理 circle整数egral_eq_of_differentiable_on_annulus_off_countable
  结论: {c : 复形} {r R : 实数} (h0 : 0 < r)
  证明: calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
    

Depends on / 依赖: circleIntegral, circleIntegral.integral_sub_inv_smul_sub_smul, circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable, continuousOn_const, continuousOn_id, continuousOn_id.sub, differentiableAt_id, differentiableAt_id.sub_const, integral_sub_inv_smul_sub_smul, sub_const
-/
theorem circleIntegral_eq_of_differentiable_on_annulus_off_countable {c : Complex} {r R : Real} (h0 : 0 < r)
    (hle : r <= R) {f : Complex -> E} {s : Set Complex} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : forall z in (ball c R \ closedBall c r) \ s, DifferentiableAt Complex f z) :
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

/--
theorem `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto` / 定理 `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`

English:
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
  statement: {c : Complex}
  proof: by
  rw [← sub_eq_zero]; rw [← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : exists δ > (0 : Real), forall z in closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy 

中文:
定理 circle整数egral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
  结论: {c : 复形}
  证明: by
  rw [← sub_eq_zero]; rw [← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : exists δ > (0 : Real), forall z in closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy 

Depends on / 依赖: Real.two_pi_pos, closedBa, closedBall, div_pos, le_of_forall_gt_imp_ge_of_dense, lt_min, min_le_left, min_le_right, nhdsWithin_hasBasis, nhds_basis_ball, nhds_basis_closedBall, norm_le_zero_iff, sub_eq_zero, subseteq, tendsto_iff, two_pi_pos
-/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto {c : Complex}
    {R : Real} (h0 : 0 < R) {f : Complex -> E} {y : E} {s : Set Complex} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ {c}))
    (hd : forall z in (ball c R \ {c}) \ s, DifferentiableAt Complex f z) (hy : Tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : Complex) • y := by
  rw [← sub_eq_zero]; rw [← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : exists δ > (0 : Real), forall z in closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 Real.two_pi_pos)
  obtain ⟨r, hr0, hrδ, hrR⟩ : exists r, 0 < r ∧ r <= δ ∧ r <= R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩
  have hsub : closedBall c R \ ball c r subseteq closedBall c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_ball_self hr0)
  have hsub' : ball c R \ closedBall c r subseteq ball c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_closedBall_self hr0.le)
  have hzne : forall z in sphere c r, z != c := fun z hz =>
ne_of_mem_of_not_mem hz fun h => hr0.ne' dist_self c ▸ Eq.symm h
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
(continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 hzne _ hz
      rw [circleIntegral.integral_sub] <;> refine (hc'.smul ?_).circleIntegrable hr0.le
· exact hc.mono subset_inter
          (sphere_subset_closedBall.trans <| closedBall_subset_closedBall hrR) hzne
      · exact continuousOn_const
    _ <= 2 * π * r * (r⁻¹ * (ε / (2 * π))) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => ?_
      specialize hzne z hz
      rw [mem_sphere]; rw [dist_eq_norm] at hz
      rw [norm_smul]; rw [norm_inv]; rw [hz]; rw [← dist_eq_norm]
      refine mul_le_mul_of_nonneg_left (hδ _ ⟨?_, hzne⟩).le (inv_nonneg.2 hr0.le)
      rwa [mem_closedBall_iff_norm, hz]
    _ = ε := by field

/--
theorem `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable` / 定理 `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`

English:
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
  statement: {R : Real} (h0 : 0 < R)
  proof: circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono sdiff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt

omit [CompleteSpace E] in

中文:
定理 circle整数egral_sub_center_inv_smul_of_differentiable_on_off_countable
  结论: {R : 实数} (h0 : 0 < R)
  证明: circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono sdiff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt

omit [CompleteSpace E] in

Depends on / 依赖: circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto, closedBall_mem_nhds, continuousAt, continuousWithinAt, hc.continuousAt, hc.mono, sdiff_subset
-/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R : Real} (h0 : 0 < R)
    {f : Complex -> E} {c : Complex} {s : Set Complex} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I) • f c :=
  circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono sdiff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt

omit [CompleteSpace E] in
/--
theorem `circleIntegral_eq_zero_of_differentiable_on_off_countable` / 定理 `circleIntegral_eq_zero_of_differentiable_on_off_countable`

English:
theorem circleIntegral_eq_zero_of_differentiable_on_off_countable
  statement: {R : Real} (h0 : 0 <= R) {f : Complex -> E}
  proof: by
  wlog hE : CompleteSpace E generalizing
  · simp [circleIntegral, intervalIntegral, integral, hE]
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_i

中文:
定理 circle整数egral_eq_zero_of_differentiable_on_off_countable
  结论: {R : 实数} (h0 : 0 <= R) {f : 复形 -> E}
  证明: by
  wlog hE : CompleteSpace E generalizing
  · simp [circleIntegral, intervalIntegral, integral, hE]
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_i

Depends on / 依赖: CompleteSpace, circleIntegral, circleIntegral.integral_radius_zero, circleIntegral.integral_sub_inv_smul_sub_smul, circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable, continuousOn_const, continuousOn_id, continuousOn_id.sub, eq_or_lt, generalizing, h0.eq_or_lt, integral, integral_radius_zero, integral_sub_inv_smul_sub_smul, intervalIntegral
-/
theorem circleIntegral_eq_zero_of_differentiable_on_off_countable {R : Real} (h0 : 0 <= R) {f : Complex -> E}
    {c : Complex} {s : Set Complex} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) : (∮ z in C(c, R), f z) = 0 := by
  wlog hE : CompleteSpace E generalizing
  · simp [circleIntegral, intervalIntegral, integral, hE]
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = (2 * ↑π * I : Complex) • (c - c) • f c :=
      (circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
        ((continuousOn_id.sub continuousOn_const).smul hc) fun z hz =>
        (differentiableAt_id.sub_const _).smul (hd z hz))
    _ = 0 := by rw [sub_self, zero_smul, smul_zero]

omit [CompleteSpace E] in
/--
theorem `_root_.DiffContOnCl.circleIntegral_eq_zero` / 定理 `_root_.DiffContOnCl.circleIntegral_eq_zero`

English:
theorem _root_.DiffContOnCl.circleIntegral_eq_zero
  statement: {R : Real} (h0 : 0 <= R) {f : Complex -> E}
  proof: circleIntegral_eq_zero_of_differentiable_on_off_countable h0 countable_empty
    hc.continuousOn_ball fun _z hz => hc.differentiableAt isOpen_ball hz.1

中文:
定理 _root_.DiffContOnCl.circle整数egral_eq_zero
  结论: {R : 实数} (h0 : 0 <= R) {f : 复形 -> E}
  证明: circleIntegral_eq_zero_of_differentiable_on_off_countable h0 countable_empty
    hc.continuousOn_ball fun _z hz => hc.differentiableAt isOpen_ball hz.1

Depends on / 依赖: circleIntegral_eq_zero_of_differentiable_on_off_countable, continuousOn_ball, countable_empty, differentiableAt, hc.continuousOn_ball, hc.differentiableAt, isOpen_ball
-/
theorem _root_.DiffContOnCl.circleIntegral_eq_zero {R : Real} (h0 : 0 <= R) {f : Complex -> E}
    {c : Complex} (hc : DiffContOnCl Complex f (ball c R)) : ∮ z in C(c, R), f z = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable h0 countable_empty
    hc.continuousOn_ball fun _z hz => hc.differentiableAt isOpen_ball hz.1

/--
theorem `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux` / 定理 `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux`

English:
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux
  statement: {R : Real} {c w : Complex}
  proof: by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : Complex -> E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : forall z in ball (c : Co

中文:
定理 circle整数egral_sub_inv_smul_of_differentiable_on_off_countable_aux
  结论: {R : 实数} {c w : 复形}
  证明: by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : Complex -> E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : forall z in ball (c : Co

Depends on / 依赖: ContinuousOn, Countable, DifferentiableAt, closedBall, closedBall_mem_nhds_of_mem, continuousOn_dslope, differentiableAt_dslope_of_ne, dist_nonneg, dist_nonneg.trans_lt, dslope, hs.insert, insert, mem_insert, ne_of_mem_of_not_mem, sdiff_subset_sdiff_right, subset_insert, trans_lt
-/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : Real} {c w : Complex}
    {f : Complex -> E} {s : Set Complex} (hs : s.Countable) (hw : w in ball c R \ s)
    (hc : ContinuousOn f (closedBall c R)) (hd : forall x in ball c R \ s, DifferentiableAt Complex f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : Complex) • f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : Complex -> E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : forall z in ball (c : Complex) R \ insert w s, DifferentiableAt Complex F z := fun z hz =>
    (differentiableAt_dslope_of_ne (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (sdiff_subset_sdiff_right (subset_insert _ _) hz))
  have HI := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF
  have hne : forall z in sphere c R, z != w := fun z hz => ne_of_mem_of_not_mem hz (ne_of_lt hw.1)
  have hFeq : EqOn F (fun z => (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R) := fun z hz =>
    calc
      F z = (z - w)⁻¹ • (f z - f w) := update_of_ne (hne z hz) ..
      _ = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w := smul_sub _ _ _
  have hc' : ContinuousOn (fun z => (z - w)⁻¹) (sphere c R) :=
(continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 hne z hz
  rw [← circleIntegral.integral_sub_inv_of_mem_ball hw.1]; rw [← circleIntegral.integral_smul_const]; rw [←
    sub_eq_zero]; rw [← circleIntegral.integral_sub]; rw [← circleIntegral.integral_congr hR.le hFeq]; rw [HI]
  exacts [(hc'.smul (hc.mono sphere_subset_closedBall)).circleIntegrable hR.le,
    (hc'.smul continuousOn_const).circleIntegrable hR.le]

/--
theorem `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` / 定理 `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`

English:
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  statement: {R : Real}
  proof: by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w in closure (ball c R \ s) by
    lift R to Real>=0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_

中文:
定理 two_pi_I_inv_smul_circle整数egral_sub_inv_smul_of_differentiable_on_off_countable
  结论: {R : 实数}
  证明: by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w in closure (ball c R \ s) by
    lift R to Real>=0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_

Depends on / 依赖: ContinuousAt, Metric, Metric.eball_coe, Metric.isOpen_eball.mem_nhds, R.coe_nonneg, circleIntegrable, closedBall_mem_nhds_of_mem, closure, coe_nonneg, continuousAt, continuousOn, dist_nonneg, dist_nonneg.trans_lt, eball_coe, hR.le, hasFPowerSeriesOn_cauchy_integral, hc.continuousAt, hc.mono, isOpen_eball, mem_nhds
-/
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : Real}
    {c w : Complex} {f : Complex -> E} {s : Set Complex} (hs : s.Countable) (hw : w in ball c R)
    (hc : ContinuousOn f (closedBall c R)) (hd : forall x in ball c R \ s, DifferentiableAt Complex f x) :
    ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w in closure (ball c R \ s) by
    lift R to Real>=0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg) hR
      refine this.continuousOn.continuousAt (Metric.isOpen_eball.mem_nhds ?_)
      rwa [Metric.eball_coe]
    have B : ContinuousAt f w := hc.continuousAt (closedBall_mem_nhds_of_mem hw)
    refine tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono ?_)
    intro z hz
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd]; rw [inv_smul_smul₀]
    simp [Real.pi_ne_zero, I_ne_zero]
  refine mem_closure_iff_nhds.2 fun t ht => ?_
  -- TODO: generalize to any vector space over `ℝ`
  set g : Real -> Complex := fun x => w + ofReal x
  have : Tendsto g (𝓝 0) (𝓝 w) := Continuous.tendsto' (by fun_prop) 0 w (add_zero _)
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this <| inter_mem ht <| isOpen_ball.mem_nhds hw) with
    ⟨l, u, hlu₀, hlu_sub⟩
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).Nonempty := by
    refine sdiff_nonempty.2 fun hsub => ?_
    have : (Ioo l u).Countable :=
      (hs.preimage ((add_right_injective w).comp ofReal_injective)).mono hsub
    rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this
    exact this.not_gt Cardinal.aleph0_lt_continuum
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩

/--
theorem `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` / 定理 `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`

English:
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  statement: {R : Real} {c w : Complex} {f : Complex -> E}
  proof: by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd]; rw [smul_inv_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

中文:
定理 circle整数egral_sub_inv_smul_of_differentiable_on_off_countable
  结论: {R : 实数} {c w : 复形} {f : 复形 -> E}
  证明: by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd]; rw [smul_inv_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

Depends on / 依赖: I_ne_zero, Real.pi_ne_zero, pi_ne_zero, two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
-/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : Real} {c w : Complex} {f : Complex -> E}
    {s : Set Complex} (hs : s.Countable) (hw : w in ball c R) (hc : ContinuousOn f (closedBall c R))
    (hd : forall x in ball c R \ s, DifferentiableAt Complex f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : Complex) • f w := by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd]; rw [smul_inv_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

/--
theorem `_root_.DiffContOnCl.circleIntegral_sub_inv_smul` / 定理 `_root_.DiffContOnCl.circleIntegral_sub_inv_smul`

English:
theorem _root_.DiffContOnCl.circleIntegral_sub_inv_smul
  statement: {R : Real} {c w : Complex} {f : Complex -> E}
  proof: circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1

中文:
定理 _root_.DiffContOnCl.circle整数egral_sub_inv_smul
  结论: {R : 实数} {c w : 复形} {f : 复形 -> E}
  证明: circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1

Depends on / 依赖: circleIntegral_sub_inv_smul_of_differentiable_on_off_countable, continuousOn_ball, countable_empty, differentiableAt, h.continuousOn_ball, h.differentiableAt, isOpen_ball
-/
theorem _root_.DiffContOnCl.circleIntegral_sub_inv_smul {R : Real} {c w : Complex} {f : Complex -> E}
    (h : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : Complex) • f w :=
  circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1

/--
theorem `_root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` / 定理 `_root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`

English:
theorem _root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
  statement: {R : Real} {c w : Complex}
  proof: by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [sdiff_emp

中文:
定理 _root_.DiffContOnCl.two_pi_i_inv_smul_circle整数egral_sub_inv_smul
  结论: {R : 实数} {c w : 复形}
  证明: by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [sdiff_emp

Depends on / 依赖: Set.nonempty_of_mem, ball_eq_empty, ball_eq_empty.not.mp, closure_ball, continuousOn, countable_empty, differentiableAt, hR.ne.symm, hf.continuousOn, hf.differentiableAt, isOpen_ball, ne_empty, nonempty_of_mem, not_le, not_le.mp, sdiff_empty, two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
-/
theorem _root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul {R : Real} {c w : Complex}
    {f : Complex -> E} (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [sdiff_empty] using fun z hz => hf.differentiableAt isOpen_ball hz

/--
theorem `_root_.DifferentiableOn.circleIntegral_sub_inv_smul` / 定理 `_root_.DifferentiableOn.circleIntegral_sub_inv_smul`

English:
theorem _root_.DifferentiableOn.circleIntegral_sub_inv_smul
  statement: {R : Real} {c w : Complex} {f : Complex -> E}
  proof: (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw

中文:
定理 _root_.DifferentiableOn.circle整数egral_sub_inv_smul
  结论: {R : 实数} {c w : 复形} {f : 复形 -> E}
  证明: (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw

Depends on / 依赖: circleIntegral_sub_inv_smul, closure_ball_subset_closedBall, diffContOnCl, diffContOnCl.circleIntegral_sub_inv_smul, hd.mono
-/
theorem _root_.DifferentiableOn.circleIntegral_sub_inv_smul {R : Real} {c w : Complex} {f : Complex -> E}
    (hd : DifferentiableOn Complex f (closedBall c R)) (hw : w in ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : Complex) • f w :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw

/--
theorem `circleIntegral_div_sub_of_differentiable_on_off_countable` / 定理 `circleIntegral_div_sub_of_differentiable_on_off_countable`

English:
theorem circleIntegral_div_sub_of_differentiable_on_off_countable
  statement: {R : Real} {c w : Complex} {s : Set Complex}
  proof: by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

中文:
定理 circle整数egral_div_sub_of_differentiable_on_off_countable
  结论: {R : 实数} {c w : 复形} {s : 集合 复形}
  证明: by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

Depends on / 依赖: circleIntegral_sub_inv_smul_of_differentiable_on_off_countable, div_eq_inv_mul, smul_eq_mul
-/
theorem circleIntegral_div_sub_of_differentiable_on_off_countable {R : Real} {c w : Complex} {s : Set Complex}
    (hs : s.Countable) (hw : w in ball c R) {f : Complex -> Complex} (hc : ContinuousOn f (closedBall c R))
    (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w := by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

end circle

section analyticity
/-!
## Applications to analyticity
-/

/--
theorem `hasFPowerSeriesOnBall_of_differentiable_off_countable` / 定理 `hasFPowerSeriesOnBall_of_differentiable_off_countable`

English:
theorem hasFPowerSeriesOnBall_of_differentiable_off_countable
  statement: {R : Real>=0} {c : Complex} {f : Complex -> E}
  proof: le_radius_cauchyPowerSeries _ _ _
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : c + w in ball c R := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
        NNReal.coe_lt_coe, enorm_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegra

中文:
定理 hasFPowerSeriesOnBall_of_differentiable_off_countable
  结论: {R : 实数>=0} {c : 复形} {f : 复形 -> E}
  证明: le_radius_cauchyPowerSeries _ _ _
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : c + w in ball c R := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
        NNReal.coe_lt_coe, enorm_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegra

Depends on / 依赖: le_radius_cauchyPowerSeries
-/
theorem hasFPowerSeriesOnBall_of_differentiable_off_countable {R : Real>=0} {c : Complex} {f : Complex -> E}
    {s : Set Complex} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R where
  r_le := le_radius_cauchyPowerSeries _ _ _
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : c + w in ball c R := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
        NNReal.coe_lt_coe, enorm_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      hs hw' hc hd]
    exact (hasFPowerSeriesOn_cauchy_integral
      ((hc.mono sphere_subset_closedBall).circleIntegrable R.2) hR).hasSum hw

/--
theorem `_root_.DiffContOnCl.hasFPowerSeriesOnBall` / 定理 `_root_.DiffContOnCl.hasFPowerSeriesOnBall`

English:
theorem _root_.DiffContOnCl.hasFPowerSeriesOnBall
  statement: {R : Real>=0} {c : Complex} {f : Complex -> E}
  proof: hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR

中文:
定理 _root_.DiffContOnCl.hasFPowerSeriesOnBall
  结论: {R : 实数>=0} {c : 复形} {f : 复形 -> E}
  证明: hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR

Depends on / 依赖: continuousOn_ball, countable_empty, differentiableAt, hasFPowerSeriesOnBall_of_differentiable_off_countable, hf.continuousOn_ball, hf.differentiableAt, isOpen_ball
-/
theorem _root_.DiffContOnCl.hasFPowerSeriesOnBall {R : Real>=0} {c : Complex} {f : Complex -> E}
    (hf : DiffContOnCl Complex f (ball c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR

/--
theorem `_root_.DifferentiableOn.hasFPowerSeriesOnBall` / 定理 `_root_.DifferentiableOn.hasFPowerSeriesOnBall`

English:
theorem _root_.DifferentiableOn.hasFPowerSeriesOnBall
  statement: {R : Real>=0} {c : Complex} {f : Complex -> E}
  proof: (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR

中文:
定理 _root_.DifferentiableOn.hasFPowerSeriesOnBall
  结论: {R : 实数>=0} {c : 复形} {f : 复形 -> E}
  证明: (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR
-/
protected theorem _root_.DifferentiableOn.hasFPowerSeriesOnBall {R : Real>=0} {c : Complex} {f : Complex -> E}
    (hd : DifferentiableOn Complex f (closedBall c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR

/--
theorem `_root_.DifferentiableOn.analyticAt` / 定理 `_root_.DifferentiableOn.analyticAt`

English:
theorem _root_.DifferentiableOn.analyticAt
  statement: {s : Set Complex} {f : Complex -> E} {z : Complex}
  proof: by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt

中文:
定理 _root_.DifferentiableOn.analyticAt
  结论: {s : 集合 复形} {f : 复形 -> E} {z : 复形}
  证明: by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt
-/
protected theorem _root_.DifferentiableOn.analyticAt {s : Set Complex} {f : Complex -> E} {z : Complex}
    (hd : DifferentiableOn Complex f s) (hz : s in 𝓝 z) : AnalyticAt Complex f z := by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt

/--
theorem `_root_.DifferentiableOn.analyticOnNhd` / 定理 `_root_.DifferentiableOn.analyticOnNhd`

English:
theorem _root_.DifferentiableOn.analyticOnNhd
  statement: {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
  proof: fun _z hz => hd.analyticAt (hs.mem_nhds hz)

中文:
定理 _root_.DifferentiableOn.analyticOnNhd
  结论: {s : 集合 复形} {f : 复形 -> E} (hd : DifferentiableOn 复形 f s)
  证明: fun _z hz => hd.analyticAt (hs.mem_nhds hz)

Depends on / 依赖: analyticAt, hd.analyticAt, hs.mem_nhds, mem_nhds
-/
theorem _root_.DifferentiableOn.analyticOnNhd {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
    (hs : IsOpen s) : AnalyticOnNhd Complex f s := fun _z hz => hd.analyticAt (hs.mem_nhds hz)

/--
theorem `_root_.DifferentiableOn.analyticOn` / 定理 `_root_.DifferentiableOn.analyticOn`

English:
theorem _root_.DifferentiableOn.analyticOn
  statement: {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
  proof: (hd.analyticOnNhd hs).analyticOn

中文:
定理 _root_.DifferentiableOn.analyticOn
  结论: {s : 集合 复形} {f : 复形 -> E} (hd : DifferentiableOn 复形 f s)
  证明: (hd.analyticOnNhd hs).analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd, hd.analyticOnNhd
-/
theorem _root_.DifferentiableOn.analyticOn {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
    (hs : IsOpen s) : AnalyticOn Complex f s :=
  (hd.analyticOnNhd hs).analyticOn

/--
theorem `_root_.DifferentiableOn.contDiffOn` / 定理 `_root_.DifferentiableOn.contDiffOn`

English:
theorem _root_.DifferentiableOn.contDiffOn
  statement: {s : Set Complex} {f : Complex -> E} {n : WithTop Nat∞}
  proof: (hd.analyticOnNhd hs).contDiffOn_of_completeSpace

中文:
定理 _root_.DifferentiableOn.contDiffOn
  结论: {s : 集合 复形} {f : 复形 -> E} {n : WithTop 自然数∞}
  证明: (hd.analyticOnNhd hs).contDiffOn_of_completeSpace
-/
protected theorem _root_.DifferentiableOn.contDiffOn {s : Set Complex} {f : Complex -> E} {n : WithTop Nat∞}
    (hd : DifferentiableOn Complex f s) (hs : IsOpen s) : ContDiffOn Complex n f s :=
  (hd.analyticOnNhd hs).contDiffOn_of_completeSpace

/--
theorem `_root_.DifferentiableOn.deriv` / 定理 `_root_.DifferentiableOn.deriv`

English:
theorem _root_.DifferentiableOn.deriv
  statement: {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
  proof: (hd.analyticOnNhd hs).deriv.differentiableOn

中文:
定理 _root_.DifferentiableOn.deriv
  结论: {s : 集合 复形} {f : 复形 -> E} (hd : DifferentiableOn 复形 f s)
  证明: (hd.analyticOnNhd hs).deriv.differentiableOn

Depends on / 依赖: analyticOnNhd, deriv.differentiableOn, differentiableOn, hd.analyticOnNhd
-/
theorem _root_.DifferentiableOn.deriv {s : Set Complex} {f : Complex -> E} (hd : DifferentiableOn Complex f s)
    (hs : IsOpen s) : DifferentiableOn Complex (deriv f) s :=
  (hd.analyticOnNhd hs).deriv.differentiableOn

/--
theorem `_root_.Differentiable.analyticAt` / 定理 `_root_.Differentiable.analyticAt`

English:
theorem _root_.Differentiable.analyticAt
  given: {f : Complex -> E} (hf : Differentiable Complex f) (z : Complex)
  proof: hf.differentiableOn.analyticAt univ_mem

中文:
定理 _root_.可微.analyticAt
  条件: {f : 复形 -> E} (hf : 可微 复形 f) (z : 复形)
  证明: hf.differentiableOn.analyticAt univ_mem
-/
protected theorem _root_.Differentiable.analyticAt {f : Complex -> E} (hf : Differentiable Complex f) (z : Complex) :
    AnalyticAt Complex f z :=
  hf.differentiableOn.analyticAt univ_mem

/--
theorem `_root_.Differentiable.contDiff` / 定理 `_root_.Differentiable.contDiff`

English:
theorem _root_.Differentiable.contDiff
  proof: contDiff_iff_contDiffAt.mpr fun z => (hf.analyticAt z).contDiffAt

@[fun_prop]

中文:
定理 _root_.可微.contDiff
  证明: contDiff_iff_contDiffAt.mpr fun z => (hf.analyticAt z).contDiffAt

@[fun_prop]
-/
protected theorem _root_.Differentiable.contDiff
    {f : Complex -> E} (hf : Differentiable Complex f) {n : WithTop Nat∞} :
    ContDiff Complex n f :=
  contDiff_iff_contDiffAt.mpr fun z => (hf.analyticAt z).contDiffAt

@[fun_prop]
/--
theorem `_root_.Differentiable.deriv` / 定理 `_root_.Differentiable.deriv`

English:
theorem _root_.Differentiable.deriv
  given: {f : Complex -> E} (hf : Differentiable Complex f)
  proof: hf.contDiff.differentiable_deriv_two

中文:
定理 _root_.可微.deriv
  条件: {f : 复形 -> E} (hf : 可微 复形 f)
  证明: hf.contDiff.differentiable_deriv_two

Depends on / 依赖: contDiff, differentiable_deriv_two, hf.contDiff.differentiable_deriv_two
-/
theorem _root_.Differentiable.deriv {f : Complex -> E} (hf : Differentiable Complex f) :
    Differentiable Complex (deriv f) :=
  hf.contDiff.differentiable_deriv_two

/--
theorem `_root_.Differentiable.hasFPowerSeriesOnBall` / 定理 `_root_.Differentiable.hasFPowerSeriesOnBall`

English:
theorem _root_.Differentiable.hasFPowerSeriesOnBall
  statement: {f : Complex -> E} (h : Differentiable Complex f)
  proof: (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩

中文:
定理 _root_.可微.hasFPowerSeriesOnBall
  结论: {f : 复形 -> E} (h : 可微 复形 f)
  证明: (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩
-/
protected theorem _root_.Differentiable.hasFPowerSeriesOnBall {f : Complex -> E} (h : Differentiable Complex f)
    (z : Complex) {R : Real>=0} (hR : 0 < R) : HasFPowerSeriesOnBall f (cauchyPowerSeries f z R) z ∞ :=
  (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩

/--
theorem `analyticOnNhd_iff_differentiableOn` / 定理 `analyticOnNhd_iff_differentiableOn`

English:
theorem analyticOnNhd_iff_differentiableOn
  given: {f : Complex -> E} {s : Set Complex} (o : IsOpen s)
  proof: ⟨AnalyticOnNhd.differentiableOn, fun d _ zs => d.analyticAt (o.mem_nhds zs)⟩

中文:
定理 analyticOnNhd_iff_differentiableOn
  条件: {f : 复形 -> E} {s : 集合 复形} (o : 是开集 s)
  证明: ⟨AnalyticOnNhd.differentiableOn, fun d _ zs => d.analyticAt (o.mem_nhds zs)⟩

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.differentiableOn, analyticAt, d.analyticAt, differentiableOn, mem_nhds, o.mem_nhds
-/
theorem analyticOnNhd_iff_differentiableOn {f : Complex -> E} {s : Set Complex} (o : IsOpen s) :
    AnalyticOnNhd Complex f s ↔ DifferentiableOn Complex f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun d _ zs => d.analyticAt (o.mem_nhds zs)⟩

/--
theorem `analyticOn_iff_differentiableOn` / 定理 `analyticOn_iff_differentiableOn`

English:
theorem analyticOn_iff_differentiableOn
  given: {f : Complex -> E} {s : Set Complex} (o : IsOpen s)
  proof: by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o

中文:
定理 analyticOn_iff_differentiableOn
  条件: {f : 复形 -> E} {s : 集合 复形} (o : 是开集 s)
  证明: by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o

Depends on / 依赖: analyticOnNhd_iff_differentiableOn, analyticOn_iff_analyticOnNhd, o.analyticOn_iff_analyticOnNhd
-/
theorem analyticOn_iff_differentiableOn {f : Complex -> E} {s : Set Complex} (o : IsOpen s) :
    AnalyticOn Complex f s ↔ DifferentiableOn Complex f s := by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o

/--
theorem `analyticOnNhd_univ_iff_differentiable` / 定理 `analyticOnNhd_univ_iff_differentiable`

English:
theorem analyticOnNhd_univ_iff_differentiable
  given: {f : Complex -> E}
  proof: by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ

中文:
定理 analyticOnNhd_univ_iff_differentiable
  条件: {f : 复形 -> E}
  证明: by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ

Depends on / 依赖: analyticOnNhd_iff_differentiableOn, differentiableOn_univ, isOpen_univ
-/
theorem analyticOnNhd_univ_iff_differentiable {f : Complex -> E} :
    AnalyticOnNhd Complex f univ ↔ Differentiable Complex f := by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ

/--
theorem `analyticOn_univ_iff_differentiable` / 定理 `analyticOn_univ_iff_differentiable`

English:
theorem analyticOn_univ_iff_differentiable
  given: {f : Complex -> E}
  proof: by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable

中文:
定理 analyticOn_univ_iff_differentiable
  条件: {f : 复形 -> E}
  证明: by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable

Depends on / 依赖: analyticOnNhd_univ_iff_differentiable, analyticOn_univ
-/
theorem analyticOn_univ_iff_differentiable {f : Complex -> E} :
    AnalyticOn Complex f univ ↔ Differentiable Complex f := by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable

/--
theorem `analyticAt_iff_eventually_differentiableAt` / 定理 `analyticAt_iff_eventually_differentiableAt`

English:
theorem analyticAt_iff_eventually_differentiableAt
  given: {f : Complex -> E} {c : Complex}
  proof: by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt]
    apply AnalyticAt.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd Complex f s := by
      refine DifferentiableOn.analyticOnNhd ?_ o
      intro z m
   

中文:
定理 analyticAt_iff_eventually_differentiableAt
  条件: {f : 复形 -> E} {c : 复形}
  证明: by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt]
    apply AnalyticAt.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd Complex f s := by
      refine DifferentiableOn.analyticOnNhd ?_ o
      intro z m
   

Depends on / 依赖: AnalyticAt, AnalyticAt.differentiableAt, AnalyticOnNhd, DifferentiableOn, DifferentiableOn.analyticOnNhd, _root_, _root_.eventually_nhds_iff.mp, analyticOnNhd, differentiableAt, differentiableWithinAt, eventually_analyticAt, eventually_nhds_iff, fa.eventually_analyticAt, filter_upwards
-/
theorem analyticAt_iff_eventually_differentiableAt {f : Complex -> E} {c : Complex} :
    AnalyticAt Complex f c ↔ forallᶠ z in 𝓝 c, DifferentiableAt Complex f z := by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt]
    apply AnalyticAt.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd Complex f s := by
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

variable {R : Real} {f : Complex -> E} {c : Complex} {s : Set Complex}

/--
lemma `circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable` / 引理 `circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable`

English:
lemma circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
  proof: by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := .mk R h0.le) hs hc hd h0
.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; rw [Finset.prod_const_one]; rw [one_smul] at this
  rw [← this]; rw [cauchyPowerSeries_apply]; rw [← Nat.cast_smul_eq_nsmul Com

中文:
引理 circle整数egral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
  证明: by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := .mk R h0.le) hs hc hd h0
.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; rw [Finset.prod_const_one]; rw [one_smul] at this
  rw [← this]; rw [cauchyPowerSeries_apply]; rw [← Nat.cast_smul_eq_nsmul Com

Depends on / 依赖: Finset, Finset.prod_const_one, Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, cauchyPowerSeries_apply, factorial_ne_zero, factorial_smul, h0.le, hasFPowerSeriesOnBall_of_differentiable_off_countable, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, mod_cast, mul_comm, mul_smul, n.factorial_ne_zero, one_smul, pow_succ, prod_const_one, two_pi_I_ne_zero
-/
lemma circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (h0 : 0 < R) (n : Nat) (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R)) (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c := by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := .mk R h0.le) hs hc hd h0
.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; rw [Finset.prod_const_one]; rw [one_smul] at this
  rw [← this]; rw [cauchyPowerSeries_apply]; rw [← Nat.cast_smul_eq_nsmul Complex]; rw [← mul_smul]; rw [← mul_smul]; rw [div_mul_cancel₀ _ (mod_cast n.factorial_ne_zero)]; rw [mul_inv_cancel₀ two_pi_I_ne_zero]
  simp [← mul_smul, pow_succ, mul_comm]

/--
lemma `differentiable_on_off_countable_deriv_eq_smul_circleIntegral` / 引理 `differentiable_on_off_countable_deriv_eq_smul_circleIntegral`

English:
lemma differentiable_on_off_countable_deriv_eq_smul_circleIntegral
  proof: by
  simpa using circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    h0 1 hs hc hd

中文:
引理 differentiable_on_off_countable_deriv_eq_smul_circle整数egral
  证明: by
  simpa using circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    h0 1 hs hc hd

Depends on / 依赖: circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
-/
lemma differentiable_on_off_countable_deriv_eq_smul_circleIntegral
    (h0 : 0 < R) (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : forall z in ball c R \ s, DifferentiableAt Complex f z) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    h0 1 hs hc hd

/--
lemma `_root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul` / 引理 `_root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`

English:
lemma _root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
  proof: c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx => hc.differentiableAt isOpen_ball hx.1

中文:
引理 _root_.DiffContOnCl.circle整数egral_one_div_sub_center_pow_smul
  证明: c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx => hc.differentiableAt isOpen_ball hx.1

Depends on / 依赖: Set.countable_empty, c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable, circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable, continuousOn_ball, countable_empty, differentiableAt, hc.continuousOn_ball, hc.differentiableAt, isOpen_ball
-/
lemma _root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
    (h0 : 0 < R) (n : Nat) (hc : DiffContOnCl Complex f (ball c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx => hc.differentiableAt isOpen_ball hx.1

/--
lemma `_root_.DiffContOnCl.deriv_eq_smul_circleIntegral` / 引理 `_root_.DiffContOnCl.deriv_eq_smul_circleIntegral`

English:
lemma _root_.DiffContOnCl.deriv_eq_smul_circleIntegral
  statement: (h0 : 0 < R)
  proof: by
  simpa using DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

中文:
引理 _root_.DiffContOnCl.deriv_eq_smul_circle整数egral
  结论: (h0 : 0 < R)
  证明: by
  simpa using DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

Depends on / 依赖: DiffContOnCl, DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul, circleIntegral_one_div_sub_center_pow_smul
-/
lemma _root_.DiffContOnCl.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DiffContOnCl Complex f (ball c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

/--
lemma `_root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` / 引理 `_root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`

English:
lemma _root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
  statement: (h0 : 0 < R) (n : Nat)
  proof: (hc.mono closure_ball_subset_closedBall).diffContOnCl
.circleIntegral_one_div_sub_center_pow_smul h0 n

中文:
引理 _root_.DifferentiableOn.circle整数egral_one_div_sub_center_pow_smul
  结论: (h0 : 0 < R) (n : 自然数)
  证明: (hc.mono closure_ball_subset_closedBall).diffContOnCl
.circleIntegral_one_div_sub_center_pow_smul h0 n

Depends on / 依赖: circleIntegral_one_div_sub_center_pow_smul, closure_ball_subset_closedBall, diffContOnCl, hc.mono
-/
lemma _root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul (h0 : 0 < R) (n : Nat)
    (hc : DifferentiableOn Complex f (closedBall c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  (hc.mono closure_ball_subset_closedBall).diffContOnCl
.circleIntegral_one_div_sub_center_pow_smul h0 n

/--
lemma `_root_.DifferentiableOn.deriv_eq_smul_circleIntegral` / 引理 `_root_.DifferentiableOn.deriv_eq_smul_circleIntegral`

English:
lemma _root_.DifferentiableOn.deriv_eq_smul_circleIntegral
  statement: (h0 : 0 < R)
  proof: by
  simpa using DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

中文:
引理 _root_.DifferentiableOn.deriv_eq_smul_circle整数egral
  结论: (h0 : 0 < R)
  证明: by
  simpa using DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

Depends on / 依赖: DifferentiableOn, DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul, circleIntegral_one_div_sub_center_pow_smul
-/
lemma _root_.DifferentiableOn.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DifferentiableOn Complex f (closedBall c R)) :
    ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z = (2 * π * I) • deriv f c := by
  simpa using DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

end derivatives

end Complex
