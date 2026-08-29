/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaEven a s = 1 / 2 * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`cosZeta a s = ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`.

Note that the term for `n = -a` in the first sum is omitted if `a` is an integer, and the term for
`n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

We also define completed versions of these functions with nicer functional equations (satisfying
`completedHurwitzZetaEven a s = Gammaℝ s * hurwitzZetaEven a s`, and similarly for `cosZeta`); and
modified versions with a subscript `0`, which are entire functions differing from the above by
multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems
* `hurwitzZetaEven` and `cosZeta`: the zeta functions
* `completedHurwitzZetaEven` and `completedCosZeta`: completed variants
* `differentiableAt_hurwitzZetaEven` and `differentiableAt_cosZeta`:
  differentiability away from `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `hasSum_int_hurwitzZetaEven` and `hasSum_nat_cosZeta`: relation between the zeta functions and
  the corresponding Dirichlet series for `1 < re s`.
-/

@[expose] public section
noncomputable section

open Complex Filter Topology Asymptotics Real Set MeasureTheory

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/--
Definition of `evenKernel` / `evenKernel` 的定义

English:
definition evenKernel
  signature: (a : UnitAddCircle) (x : Real)
  body: (show Function.Periodic
    (fun ξ : Real => rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this]; rw [re_ofReal_mul]; rw [← mul_assoc]; rw [← Real.exp_add]
      congr
      ring).lift a

中文:
定义 evenKernel
  签名: (a : UnitAddCircle) (x : 实数)
  定义体: (show Function.Periodic
    (fun ξ : Real => rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this]; rw [re_ofReal_mul]; rw [← mul_assoc]; rw [← Real.exp_add]
      congr
      ring).lift a
-/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : Real) : Real :=
  (show Function.Periodic
    (fun ξ : Real => rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this]; rw [re_ofReal_mul]; rw [← mul_assoc]; rw [← Real.exp_add]
      congr
      ring).lift a

/--
lemma `evenKernel_def` / 引理 `evenKernel_def`

English:
lemma evenKernel_def
  given: (a x : Real)
  proof: by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

中文:
引理 evenKernel_def
  条件: (a x : 实数)
  证明: by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

Depends on / 依赖: evenKernel, mul_two, re_eq_add_conj, two_ne_zero
-/
lemma evenKernel_def (a x : Real) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

/--
lemma `evenKernel_undef` / 引理 `evenKernel_undef`

English:
lemma evenKernel_undef
  given: (a : UnitAddCircle) {x : Real} (hx : x <= 0)
  statement: evenKernel a x = 0
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

中文:
引理 evenKernel_undef
  条件: (a : UnitAddCircle) {x : 实数} (hx : x <= 0)
  结论: evenKernel a x = 0
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, evenKernel_def, induction_on, ofReal_inj
-/
lemma evenKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : evenKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

/--
Definition of `cosKernel` / `cosKernel` 的定义

English:
definition cosKernel
  signature: (a : UnitAddCircle) (x : Real)
  body: (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a

中文:
定义 cosKernel
  签名: (a : UnitAddCircle) (x : 实数)
  定义体: (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a
-/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : Real) : Real :=
  (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a

/--
lemma `cosKernel_def` / 引理 `cosKernel_def`

English:
lemma cosKernel_def
  given: (a x : Real)
  statement: ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x)
  proof: by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

中文:
引理 cosKernel_def
  条件: (a x : 实数)
  结论: ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x)
  证明: by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

Depends on / 依赖: cosKernel, mul_two, re_eq_add_conj, two_ne_zero
-/
lemma cosKernel_def (a x : Real) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

/--
lemma `cosKernel_undef` / 引理 `cosKernel_undef`

English:
lemma cosKernel_undef
  given: (a : UnitAddCircle) {x : Real} (hx : x <= 0)
  statement: cosKernel a x = 0
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

中文:
引理 cosKernel_undef
  条件: (a : UnitAddCircle) {x : 实数} (hx : x <= 0)
  结论: cosKernel a x = 0
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, cosKernel_def, induction_on, ofReal_inj
-/
lemma cosKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : cosKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im <= 0)]

/--
lemma `evenKernel_eq_cosKernel_of_zero` / 引理 `evenKernel_eq_cosKernel_of_zero`

English:
lemma evenKernel_eq_cosKernel_of_zero
  statement: evenKernel 0 = cosKernel 0
  proof: by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]

中文:
引理 evenKernel_eq_cosKernel_of_zero
  结论: evenKernel 0 = cosKernel 0
  证明: by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk_zero, cosKernel_def, evenKernel_def, mk_zero, ofReal_inj
-/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]
/--
lemma `evenKernel_neg` / 引理 `evenKernel_neg`

English:
lemma evenKernel_neg
  given: (a : UnitAddCircle) (x : Real)
  statement: evenKernel (-a) x = evenKernel a x
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]

中文:
引理 evenKernel_neg
  条件: (a : UnitAddCircle) (x : 实数)
  结论: evenKernel (-a) x = evenKernel a x
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.mk_neg, evenKernel_def, induction_on, mk_neg, ofReal_inj
-/
lemma evenKernel_neg (a : UnitAddCircle) (x : Real) : evenKernel (-a) x = evenKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]
/--
lemma `cosKernel_neg` / 引理 `cosKernel_neg`

English:
lemma cosKernel_neg
  given: (a : UnitAddCircle) (x : Real)
  statement: cosKernel (-a) x = cosKernel a x
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]

中文:
引理 cosKernel_neg
  条件: (a : UnitAddCircle) (x : 实数)
  结论: cosKernel (-a) x = cosKernel a x
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.mk_neg, cosKernel_def, induction_on, mk_neg, ofReal_inj
-/
lemma cosKernel_neg (a : UnitAddCircle) (x : Real) : cosKernel (-a) x = cosKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]

/--
lemma `continuousOn_evenKernel` / 引理 `continuousOn_evenKernel`

English:
lemma continuousOn_evenKernel
  given: (a : UnitAddCircle)
  statement: ContinuousOn (evenKernel a) (Ioi 0)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (evenKernel a' x : Complex))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : Real => (a' * I * u, I * u)) (by fun_prop)

中文:
引理 continuousOn_evenKernel
  条件: (a : UnitAddCircle)
  结论: ContinuousOn (evenKernel a) (左开右无界区间 0)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (evenKernel a' x : Complex))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : Real => (a' * I * u, I * u)) (by fun_prop)

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, comp_continuousOn, continuousOn_of_forall_continuousAt, continuous_re, continuous_re.comp_continuousOn, evenKernel, evenKernel_def, fun_prop, induction_on
-/
lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (evenKernel a' x : Complex))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : Real => (a' * I * u, I * u)) (by fun_prop)

/--
lemma `continuousOn_cosKernel` / 引理 `continuousOn_cosKernel`

English:
lemma continuousOn_cosKernel
  given: (a : UnitAddCircle)
  statement: ContinuousOn (cosKernel a) (Ioi 0)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (cosKernel a' x : Complex))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : Real => ((a' : Complex), I * u)) (by fun_prop)

中文:
引理 continuousOn_cosKernel
  条件: (a : UnitAddCircle)
  结论: ContinuousOn (cosKernel a) (左开右无界区间 0)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (cosKernel a' x : Complex))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : Real => ((a' : Complex), I * u)) (by fun_prop)

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, comp_continuousOn, continuousOn_of_forall_continuousAt, continuous_re, continuous_re.comp_continuousOn, cosKernel, cosKernel_def, fun_prop, induction_on
-/
lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x => (cosKernel a' x : Complex))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : Real => ((a' : Complex), I * u)) (by fun_prop)

/--
lemma `evenKernel_functional_equation` / 引理 `evenKernel_functional_equation`

English:
lemma evenKernel_functional_equation
  given: (a : UnitAddCircle) (x : Real)
  proof: by
  rcases le_or_gt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction a using QuotientAddGroup.induction_on with | H a =>
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [evenKernel_def]; rw [cosKernel_def]; rw [jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div]; rw [mul_one_div]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg]
  have hx' : I * x != 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : Complex) = 1 / ↑(x ^ (1 / 2 : Real)) := by
    rw [neg_mul]; rw [← mul_assoc]; rw [I_mul_I]; rw [neg_one_mul]; rw [neg_neg]; rw [ofReal_cpow hx.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow]; rw [mul_pow]; rw [I_sq]; rw [div_eq_iff hx']
    ring
  rw [h1]; rw [h2]; rw [h3]; rw [h4]; rw [← mul_assoc]; rw [mul_comm (cexp _)]; rw [mul_assoc _ (cexp _) (cexp _)]; rw [← Complex.exp_add]; rw [neg_add_cancel]; rw [Complex.exp_zero]; rw [mul_one]; rw [ofReal_div]; rw [ofReal_one]

中文:
引理 evenKernel_functional_equation
  条件: (a : UnitAddCircle) (x : 实数)
  证明: by
  rcases le_or_gt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction a using QuotientAddGroup.induction_on with | H a =>
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [evenKernel_def]; rw [cosKernel_def]; rw [jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div]; rw [mul_one_div]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg]
  have hx' : I * x != 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : Complex) = 1 / ↑(x ^ (1 / 2 : Real)) := by
    rw [neg_mul]; rw [← mul_assoc]; rw [I_mul_I]; rw [neg_one_mul]; rw [neg_neg]; rw [ofReal_cpow hx.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow]; rw [mul_pow]; rw [I_sq]; rw [div_eq_iff hx']
    ring
  rw [h1]; rw [h2]; rw [h3]; rw [h4]; rw [← mul_assoc]; rw [mul_comm (cexp _)]; rw [mul_assoc _ (cexp _) (cexp _)]; rw [← Complex.exp_add]; rw [neg_add_cancel]; rw [Complex.exp_zero]; rw [mul_one]; rw [ofReal_div]; rw [ofReal_one]

Depends on / 依赖: I_ne_zero, QuotientAddGroup, QuotientAddGroup.induction_on, cosKernel_def, cosKernel_undef, div_I, div_div, div_nonpos_of_nonneg_of_nonpos, evenKernel_def, evenKernel_undef, induction_on, le_or_gt, mul_ne_zero, mul_one_div, mul_zero, neg_neg, neg_one_mul, ofReal_inj, ofReal_mul, zero_le_one
-/
lemma evenKernel_functional_equation (a : UnitAddCircle) (x : Real) :
    evenKernel a x = 1 / x ^ (1 / 2 : Real) * cosKernel a (1 / x) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction a using QuotientAddGroup.induction_on with | H a =>
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [evenKernel_def]; rw [cosKernel_def]; rw [jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div]; rw [mul_one_div]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg]
  have hx' : I * x != 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : Complex) = 1 / ↑(x ^ (1 / 2 : Real)) := by
    rw [neg_mul]; rw [← mul_assoc]; rw [I_mul_I]; rw [neg_one_mul]; rw [neg_neg]; rw [ofReal_cpow hx.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow]; rw [mul_pow]; rw [I_sq]; rw [div_eq_iff hx']
    ring
  rw [h1]; rw [h2]; rw [h3]; rw [h4]; rw [← mul_assoc]; rw [mul_comm (cexp _)]; rw [mul_assoc _ (cexp _) (cexp _)]; rw [← Complex.exp_add]; rw [neg_add_cancel]; rw [Complex.exp_zero]; rw [mul_one]; rw [ofReal_div]; rw [ofReal_one]

end kernel_defs

section asymp


/--
lemma `hasSum_int_evenKernel` / 引理 `hasSum_int_evenKernel`

English:
lemma hasSum_int_evenKernel
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  rw [← hasSum_ofReal]; rw [evenKernel_def]
  have (n : Int) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _

中文:
引理 hasSum_int_evenKernel
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  rw [← hasSum_ofReal]; rw [evenKernel_def]
  have (n : Int) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _

Depends on / 依赖: Complex.exp_add, I_sq, evenKernel_def, exp_add, hasSum_ofReal, mul_left
-/
lemma hasSum_int_evenKernel (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Int => rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal]; rw [evenKernel_def]
  have (n : Int) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _

/--
lemma `hasSum_int_cosKernel` / 引理 `hasSum_int_cosKernel`

English:
lemma hasSum_int_cosKernel
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  rw [cosKernel_def a t]
  have (n : Int) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

中文:
引理 hasSum_int_cosKernel
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  rw [cosKernel_def a t]
  have (n : Int) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

Depends on / 依赖: Complex.exp_add, cosKernel_def, exp_add, ring_nf, sub_eq_add_neg
-/
lemma hasSum_int_cosKernel (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Int => cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  have (n : Int) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

/--
lemma `hasSum_int_evenKernel₀` / 引理 `hasSum_int_evenKernel₀`

English:
lemma hasSum_int_evenKernel₀
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  have := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : Real) ht) (-k)
  · suffices forall (n : Int), n + a != 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩

中文:
引理 hasSum_int_evenKernel₀
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  have := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : Real) ht) (-k)
  · suffices forall (n : Int), n + a != 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩

Depends on / 依赖: AddCircle, AddCircle.coe_eq_zero_iff, Classical, Classical.propDecidable, Int.cast_add, add_eq_zero_iff_eq_neg, cast_add, coe_eq_zero_iff, contrapose, hasSum_int_evenKernel, hasSum_ite_sub_hasSum, instance, neg_eq_iff_add_eq_zero, propDecidable, search, simp_rw, split_ifs, zsmul_one
-/
lemma hasSum_int_evenKernel₀ (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Int => if n + a = 0 then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  have := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : Real) ht) (-k)
  · suffices forall (n : Int), n + a != 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩

/--
lemma `hasSum_int_cosKernel₀` / 引理 `hasSum_int_cosKernel₀`

English:
lemma hasSum_int_cosKernel₀
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

中文:
引理 hasSum_int_cosKernel₀
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

Depends on / 依赖: hasSum_int_cosKernel, hasSum_ite_sub_hasSum
-/
lemma hasSum_int_cosKernel₀ (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Int => if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

/--
lemma `hasSum_nat_cosKernel₀` / 引理 `hasSum_nat_cosKernel₀`

English:
lemma hasSum_nat_cosKernel₀
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  rw [← hasSum_ofReal]; rw [ofReal_sub]; rw [ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n => ?_
  push_cast
  rw [Complex.cos]; rw [mul_div_cancel₀ _ two_ne_zero]
  congr 3 <;> ring

中文:
引理 hasSum_nat_cosKernel₀
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  rw [← hasSum_ofReal]; rw [ofReal_sub]; rw [ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n => ?_
  push_cast
  rw [Complex.cos]; rw [mul_div_cancel₀ _ two_ne_zero]
  congr 3 <;> ring

Depends on / 依赖: Complex.co, Complex.exp_zero, Finset, Finset.sum_range_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, Nat.cast_zero, Real.exp_zero, add_mul, add_sub_assoc, cast_natCast, cast_neg, cast_zero, congr_fun, exp_zero, hasSum_int_cosKernel, hasSum_nat_add_iff, hasSum_ofReal, mul_neg
-/
lemma hasSum_nat_cosKernel₀ (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Nat => 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal]; rw [ofReal_sub]; rw [ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n => ?_
  push_cast
  rw [Complex.cos]; rw [mul_div_cancel₀ _ two_ne_zero]
  congr 3 <;> ring

/-!
## Asymptotics of the kernels as `t → ∞`
-/

/--
lemma `isBigO_atTop_evenKernel_sub` / 引理 `isBigO_atTop_evenKernel_sub`

English:
lemma isBigO_atTop_evenKernel_sub
  given: (a : UnitAddCircle)
  statement: exists p : Real, 0 < p ∧
  proof: by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

中文:
引理 isBigO_atTop_evenKernel_sub
  条件: (a : UnitAddCircle)
  结论: 存在 p : 实数, 0 < p ∧
  证明: by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

Depends on / 依赖: EventuallyEq, EventuallyEq.isBigO, F_int, HurwitzKernelBounds, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int, HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub, QuotientAddGroup, QuotientAddGroup.induction_on, eventually_gt_atTop, f_int, filter_upwards, hasSum_int_evenKernel, induction_on, isBigO, isBigO_atTop_F_int_zero_sub, tsum_eq
-/
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : exists p : Real, 0 < p ∧
    (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -p * ·) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

/--
lemma `isBigO_atTop_cosKernel_sub` / 引理 `isBigO_atTop_cosKernel_sub`

English:
lemma isBigO_atTop_cosKernel_sub
  given: (a : UnitAddCircle)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul]; rw [norm_mul]; rw [norm_two]; rw [mul_assoc]; rw [mul_le_mul_iff_of_pos_left two_pos]; rw [norm_of_nonneg (exp_pos _).le]; rw [HurwitzKernelBounds.f_nat]; rw [pow_zero]; rw [one_mul]; rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

中文:
引理 isBigO_atTop_cosKernel_sub
  条件: (a : UnitAddCircle)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul]; rw [norm_mul]; rw [norm_two]; rw [mul_assoc]; rw [mul_le_mul_iff_of_pos_left two_pos]; rw [norm_of_nonneg (exp_pos _).le]; rw [HurwitzKernelBounds.f_nat]; rw [pow_zero]; rw [one_mul]; rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

Depends on / 依赖: Eventually, Eventually.isBigO, F_nat, HurwitzKernelBounds, HurwitzKernelBounds.F_nat, HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub, HurwitzKernelBounds.summable_f_nat, QuotientAddGroup, QuotientAddGroup.induction_on, const_mul_left, eq_false_intro, eventually_gt_atTop, filter_upwards, hasSum, hasSum.mul_left, if_false, induction_on, isBigO, isBigO_atTop_F_nat_zero_sub, mul_left
-/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    exists p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x => Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul]; rw [norm_mul]; rw [norm_two]; rw [mul_assoc]; rw [mul_le_mul_iff_of_pos_left two_pos]; rw [norm_of_nonneg (exp_pos _).le]; rw [HurwitzKernelBounds.f_nat]; rw [pow_zero]; rw [one_mul]; rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/--
Definition of `hurwitzEvenFEPair` / `hurwitzEvenFEPair` 的定义

English:
definition hurwitzEvenFEPair
  signature: (a : UnitAddCircle)
  body: ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : Real -> Complex), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
simpa using isBigO_ofReal_left.mpr hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by simp [← ofReal_mul, evenKernel_functional_equation, inv_rpow (le_of_lt hx)]

@[simp]

中文:
定义 hurwitzEvenFEPair
  签名: (a : UnitAddCircle)
  定义体: ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : Real -> Complex), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
simpa using isBigO_ofReal_left.mpr hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by simp [← ofReal_mul, evenKernel_functional_equation, inv_rpow (le_of_lt hx)]

@[simp]

Depends on / 依赖: evenKernel, ofReal
-/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair Complex where
  f := ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : Real -> Complex), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
simpa using isBigO_ofReal_left.mpr hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by simp [← ofReal_mul, evenKernel_functional_equation, inv_rpow (le_of_lt hx)]

@[simp]
/--
lemma `hurwitzEvenFEPair_zero_symm` / 引理 `hurwitzEvenFEPair_zero_symm`

English:
lemma hurwitzEvenFEPair_zero_symm
  proof: by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]

中文:
引理 hurwitzEvenFEPair_zero_symm
  证明: by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]

Depends on / 依赖: WeakFEPair, WeakFEPair.symm, evenKernel_eq_cosKernel_of_zero, hurwitzEvenFEPair
-/
lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]
/--
lemma `hurwitzEvenFEPair_neg` / 引理 `hurwitzEvenFEPair_neg`

English:
lemma hurwitzEvenFEPair_neg
  given: (a : UnitAddCircle)
  statement: hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a
  proof: by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

中文:
引理 hurwitzEvenFEPair_neg
  条件: (a : UnitAddCircle)
  结论: hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a
  证明: by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, hurwitzEvenFEPair
-/
lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

/-!
## Definition of the completed even Hurwitz zeta function
-/

/--
Definition of `completedHurwitzZetaEven` / `completedHurwitzZetaEven` 的定义

English:
definition completedHurwitzZetaEven
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

中文:
定义 completedHurwitzZetaEven
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

Depends on / 依赖: hurwitzEvenFEPair
-/
def completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

/--
Definition of `completedHurwitzZetaEven₀` / `completedHurwitzZetaEven₀` 的定义

English:
definition completedHurwitzZetaEven₀
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

中文:
定义 completedHurwitzZetaEven₀
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

Depends on / 依赖: hurwitzEvenFEPair
-/
def completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

/--
lemma `completedHurwitzZetaEven_eq` / 引理 `completedHurwitzZetaEven_eq`

English:
lemma completedHurwitzZetaEven_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [completedHurwitzZetaEven]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [mul_one_div]
  · change (1 / (↑(1 / 2 : Real) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul]; rw [mul_one]; rw [← sub_div]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]

中文:
引理 completedHurwitzZetaEven_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [completedHurwitzZetaEven]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [mul_one_div]
  · change (1 / (↑(1 / 2 : Real) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul]; rw [mul_one]; rw [← sub_div]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]

Depends on / 依赖: WeakFEPair, completedHurwitzZetaEven, div_, div_div, mul_comm, mul_div_assoc, mul_one, mul_one_div, smul_eq_mul, sub_div, two_ne_zero
-/
lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaEven a s =
    completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s - 1 / (1 - s) := by
  rw [completedHurwitzZetaEven]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [mul_one_div]
  · change (1 / (↑(1 / 2 : Real) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul]; rw [mul_one]; rw [← sub_div]; rw [div_div]; rw [div_mul_cancel₀ _ two_ne_zero]

/--
Definition of `completedCosZeta` / `completedCosZeta` 的定义

English:
definition completedCosZeta
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

中文:
定义 completedCosZeta
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

Depends on / 依赖: hurwitzEvenFEPair
-/
def completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

/--
Definition of `completedCosZeta₀` / `completedCosZeta₀` 的定义

English:
definition completedCosZeta₀
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

中文:
定义 completedCosZeta₀
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

Depends on / 依赖: hurwitzEvenFEPair
-/
def completedCosZeta₀ (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

/--
lemma `completedCosZeta_eq` / 引理 `completedCosZeta_eq`

English:
lemma completedCosZeta_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [completedCosZeta]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · rw [completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex), mul_one_div]

中文:
引理 completedCosZeta_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [completedCosZeta]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · rw [completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex), mul_one_div]

Depends on / 依赖: WeakFEPair, WeakFEPair.symm, completedCosZeta, div_div, hurwitzEvenFEPair, inv_one, mul_comm, mul_div_assoc, mul_one, mul_one_div, simp_rw, smul_eq_mul, sub_div, two_ne_zero
-/
lemma completedCosZeta_eq (a : UnitAddCircle) (s : Complex) :
    completedCosZeta a s =
    completedCosZeta₀ a s - 1 / s - (if a = 0 then 1 else 0) / (1 - s) := by
  rw [completedCosZeta]; rw [WeakFEPair.Λ]; rw [sub_div]; rw [sub_div]
  congr 1
  · rw [completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel₀ _ (two_ne_zero' Complex), mul_one_div]

/-!
## Parity and functional equations
-/

@[simp]
/--
lemma `completedHurwitzZetaEven_neg` / 引理 `completedHurwitzZetaEven_neg`

English:
lemma completedHurwitzZetaEven_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedHurwitzZetaEven]

@[simp]

中文:
引理 completedHurwitzZetaEven_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedHurwitzZetaEven]

@[simp]

Depends on / 依赖: completedHurwitzZetaEven
-/
lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaEven (-a) s = completedHurwitzZetaEven a s := by
  simp [completedHurwitzZetaEven]

@[simp]
/--
lemma `completedHurwitzZetaEven₀_neg` / 引理 `completedHurwitzZetaEven₀_neg`

English:
lemma completedHurwitzZetaEven₀_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedHurwitzZetaEven₀]

@[simp]

中文:
引理 completedHurwitzZetaEven₀_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedHurwitzZetaEven₀]

@[simp]
-/
lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp [completedHurwitzZetaEven₀]

@[simp]
/--
lemma `completedCosZeta_neg` / 引理 `completedCosZeta_neg`

English:
lemma completedCosZeta_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedCosZeta]

@[simp]

中文:
引理 completedCosZeta_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedCosZeta]

@[simp]

Depends on / 依赖: completedCosZeta
-/
lemma completedCosZeta_neg (a : UnitAddCircle) (s : Complex) :
    completedCosZeta (-a) s = completedCosZeta a s := by
  simp [completedCosZeta]

@[simp]
/--
lemma `completedCosZeta₀_neg` / 引理 `completedCosZeta₀_neg`

English:
lemma completedCosZeta₀_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedCosZeta₀]

中文:
引理 completedCosZeta₀_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedCosZeta₀]
-/
lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : Complex) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp [completedCosZeta₀]

/--
lemma `completedHurwitzZetaEven_one_sub` / 引理 `completedHurwitzZetaEven_one_sub`

English:
lemma completedHurwitzZetaEven_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

中文:
引理 completedHurwitzZetaEven_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

Depends on / 依赖: completedCosZeta, completedHurwitzZetaEven, functional_equation, hurwitzEvenFEPair, one_smul, sub_div
-/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaEven a (1 - s) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven]; rw [completedCosZeta]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

/--
lemma `completedHurwitzZetaEven₀_one_sub` / 引理 `completedHurwitzZetaEven₀_one_sub`

English:
lemma completedHurwitzZetaEven₀_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation₀ (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

中文:
引理 completedHurwitzZetaEven₀_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation₀ (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

Depends on / 依赖: hurwitzEvenFEPair, one_smul, sub_div
-/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀]; rw [completedCosZeta₀]; rw [sub_div]; rw [(by simp : (1 / 2 : Complex) = ↑(1 / 2 : Real))]; rw [(by rfl : (1 / 2 : Real) = (hurwitzEvenFEPair a).k)]; rw [(hurwitzEvenFEPair a).functional_equation₀ (s / 2)]; rw [(by rfl : (hurwitzEvenFEPair a).ε = 1)]; rw [one_smul]

/--
lemma `completedCosZeta_one_sub` / 引理 `completedCosZeta_one_sub`

English:
lemma completedCosZeta_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [← completedHurwitzZetaEven_one_sub]; rw [sub_sub_cancel]

中文:
引理 completedCosZeta_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [← completedHurwitzZetaEven_one_sub]; rw [sub_sub_cancel]

Depends on / 依赖: completedHurwitzZetaEven_one_sub, sub_sub_cancel
-/
lemma completedCosZeta_one_sub (a : UnitAddCircle) (s : Complex) :
    completedCosZeta a (1 - s) = completedHurwitzZetaEven a s := by
  rw [← completedHurwitzZetaEven_one_sub]; rw [sub_sub_cancel]

/--
lemma `completedCosZeta₀_one_sub` / 引理 `completedCosZeta₀_one_sub`

English:
lemma completedCosZeta₀_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [← completedHurwitzZetaEven₀_one_sub]; rw [sub_sub_cancel]

中文:
引理 completedCosZeta₀_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [← completedHurwitzZetaEven₀_one_sub]; rw [sub_sub_cancel]

Depends on / 依赖: sub_sub_cancel
-/
lemma completedCosZeta₀_one_sub (a : UnitAddCircle) (s : Complex) :
    completedCosZeta₀ a (1 - s) = completedHurwitzZetaEven₀ a s := by
  rw [← completedHurwitzZetaEven₀_one_sub]; rw [sub_sub_cancel]

end FEPair

/-!
## Differentiability and residues
-/

section FEPair

/--
lemma `differentiableAt_completedHurwitzZetaEven` / 引理 `differentiableAt_completedHurwitzZetaEven`

English:
lemma differentiableAt_completedHurwitzZetaEven
  proof: by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rcases hs with h | h <;>
    simp [hurwitzEvenFEPair, h]
  · change s / 2 != ↑(1 / 2 : Real)
    rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

中文:
引理 differentiableAt_completedHurwitzZetaEven
  证明: by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rcases hs with h | h <;>
    simp [hurwitzEvenFEPair, h]
  · change s / 2 != ↑(1 / 2 : Real)
    rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

Depends on / 依赖: Or.inl, differentiableAt_id, differentiableAt_id.div_const, div_const, div_left_inj, hurwitzEvenFEPair, ofReal_div, ofReal_ofNat, ofReal_one, two_ne_zero
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : Complex} (hs : s != 0 ∨ a != 0) (hs' : s != 1) :
    DifferentiableAt Complex (completedHurwitzZetaEven a) s := by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rcases hs with h | h <;>
    simp [hurwitzEvenFEPair, h]
  · change s / 2 != ↑(1 / 2 : Real)
    rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

/--
lemma `differentiable_completedHurwitzZetaEven₀` / 引理 `differentiable_completedHurwitzZetaEven₀`

English:
lemma differentiable_completedHurwitzZetaEven₀
  given: (a : UnitAddCircle)
  proof: ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

中文:
引理 differentiable_completedHurwitzZetaEven₀
  条件: (a : UnitAddCircle)
  证明: ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

Depends on / 依赖: differentiable_id, differentiable_id.div_const, div_const, hurwitzEvenFEPair
-/
lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable Complex (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/--
lemma `differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven` / 引理 `differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven`

English:
lemma differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
  proof: by
  have (s : _) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
refine .sub ?_ (differentiable_const _ _).div (differentiable_id _) one_ne_zero
  apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀

中文:
引理 differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
  证明: by
  have (s : _) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
refine .sub ?_ (differentiable_const _ _).div (differentiable_id _) one_ne_zero
  apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀

Depends on / 依赖: DifferentiableAt, DifferentiableAt.sub, completedHurwitzZetaEven, completedHurwitzZetaEven_eq, differentiable_const, differentiable_id, one_ne_zero, simp_rw, sub_div
-/
lemma differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
    (a b : UnitAddCircle) :
    DifferentiableAt Complex (fun s => completedHurwitzZetaEven a s - completedHurwitzZetaEven b s) 1 := by
  have (s : _) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
refine .sub ?_ (differentiable_const _ _).div (differentiable_id _) one_ne_zero
  apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀

/--
lemma `differentiableAt_completedCosZeta` / 引理 `differentiableAt_completedCosZeta`

English:
lemma differentiableAt_completedCosZeta
  proof: by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · exact div_ne_zero_iff.mpr ⟨hs, two_ne_zero⟩
  · change s / 2 != ↑(1 / 2 : Real) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h => ?_) (fun ha => ?_) hs'
    · simpa [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simpa

中文:
引理 differentiableAt_completedCosZeta
  证明: by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · exact div_ne_zero_iff.mpr ⟨hs, two_ne_zero⟩
  · change s / 2 != ↑(1 / 2 : Real) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h => ?_) (fun ha => ?_) hs'
    · simpa [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simpa

Depends on / 依赖: Or.imp, Or.inl, differentiableAt_id, differentiableAt_id.div_const, div_const, div_left_inj, div_ne_zero_iff, div_ne_zero_iff.mpr, hurwitzEvenFEPair, symm.differentiableAt_, two_ne_zero
-/
lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : Complex} (hs : s != 0) (hs' : s != 1 ∨ a != 0) :
    DifferentiableAt Complex (completedCosZeta a) s := by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · exact div_ne_zero_iff.mpr ⟨hs, two_ne_zero⟩
  · change s / 2 != ↑(1 / 2 : Real) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h => ?_) (fun ha => ?_) hs'
    · simpa [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simpa

/--
lemma `differentiable_completedCosZeta₀` / 引理 `differentiable_completedCosZeta₀`

English:
lemma differentiable_completedCosZeta₀
  given: (a : UnitAddCircle)
  proof: ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

中文:
引理 differentiable_completedCosZeta₀
  条件: (a : UnitAddCircle)
  证明: ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

Depends on / 依赖: differentiable_id, differentiable_id.div_const, div_const, hurwitzEvenFEPair, symm.differentiable_
-/
lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable Complex (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/--
lemma `tendsto_div_two_punctured_nhds` / 引理 `tendsto_div_two_punctured_nhds`

English:
lemma tendsto_div_two_punctured_nhds
  given: (a : Complex)
  proof: le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' Complex))).map_punctured_nhds_eq a)

中文:
引理 tendsto_div_two_punctured_nhds
  条件: (a : 复形)
  证明: le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' Complex))).map_punctured_nhds_eq a)
-/
private lemma tendsto_div_two_punctured_nhds (a : Complex) :
    Tendsto (fun s : Complex => s / 2) (𝓝[!=] a) (𝓝[!=] (a / 2)) :=
  le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' Complex))).map_punctured_nhds_eq a)

/--
lemma `completedHurwitzZetaEven_residue_one` / 引理 `completedHurwitzZetaEven_residue_one`

English:
lemma completedHurwitzZetaEven_residue_one
  given: (a : UnitAddCircle)
  proof: by
  have h1 : Tendsto (fun s : Complex => (s - ↑(1 / 2 : Real)) * _) (𝓝[!=] ↑(1 / 2 : Real))
    (𝓝 ((1 : Complex) * (1 : Complex))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  refine (h1.comp <| tendsto_div_two_punctured_nhds 1).congr (fun s => ?_)
  rw [completedHurwitzZetaEven]; rw [Function.comp_apply]; rw [← sub_div]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

中文:
引理 completedHurwitzZetaEven_residue_one
  条件: (a : UnitAddCircle)
  证明: by
  have h1 : Tendsto (fun s : Complex => (s - ↑(1 / 2 : Real)) * _) (𝓝[!=] ↑(1 / 2 : Real))
    (𝓝 ((1 : Complex) * (1 : Complex))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  refine (h1.comp <| tendsto_div_two_punctured_nhds 1).congr (fun s => ?_)
  rw [completedHurwitzZetaEven]; rw [Function.comp_apply]; rw [← sub_div]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

Depends on / 依赖: Function, Function.comp_apply, Tendsto, comp_apply, completedHurwitzZetaEven, div_mul_eq_mul_div, h1.comp, hurwitzEvenFEPair, mul_div_assoc, one_mul, sub_div, tendsto_div_two_punctured_nhds
-/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s => (s - 1) * completedHurwitzZetaEven a s) (𝓝[!=] 1) (𝓝 1) := by
  have h1 : Tendsto (fun s : Complex => (s - ↑(1 / 2 : Real)) * _) (𝓝[!=] ↑(1 / 2 : Real))
    (𝓝 ((1 : Complex) * (1 : Complex))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  refine (h1.comp <| tendsto_div_two_punctured_nhds 1).congr (fun s => ?_)
  rw [completedHurwitzZetaEven]; rw [Function.comp_apply]; rw [← sub_div]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

/--
lemma `completedHurwitzZetaEven_residue_zero` / 引理 `completedHurwitzZetaEven_residue_zero`

English:
lemma completedHurwitzZetaEven_residue_zero
  given: (a : UnitAddCircle)
  proof: by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : Complex) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast] at h1
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedHurwitzZetaEven, div_mul_eq_mul_div, mul_div_assoc]

中文:
引理 completedHurwitzZetaEven_residue_zero
  条件: (a : UnitAddCircle)
  证明: by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : Complex) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast] at h1
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedHurwitzZetaEven, div_mul_eq_mul_div, mul_div_assoc]

Depends on / 依赖: Tendsto, completedHurwitzZetaEven, div_mul_eq_mul_div, h1.comp, hurwitzEvenFEPair, mul_div_assoc, split_ifs, tendsto_div_two_punctured_nhds, zero_div
-/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s => s * completedHurwitzZetaEven a s) (𝓝[!=] 0) (𝓝 (if a = 0 then -1 else 0)) := by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : Complex) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast] at h1
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedHurwitzZetaEven, div_mul_eq_mul_div, mul_div_assoc]

/--
lemma `completedCosZeta_residue_zero` / 引理 `completedCosZeta_residue_zero`

English:
lemma completedCosZeta_residue_zero
  given: (a : UnitAddCircle)
  proof: by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedCosZeta, div_mul_eq_mul_div, mul_div_assoc]

中文:
引理 completedCosZeta_residue_zero
  条件: (a : UnitAddCircle)
  证明: by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedCosZeta, div_mul_eq_mul_div, mul_div_assoc]

Depends on / 依赖: Tendsto, completedCosZeta, div_mul_eq_mul_div, h1.comp, hurwitzEvenFEPair, mul_div_assoc, tendsto_div_two_punctured_nhds, zero_div
-/
lemma completedCosZeta_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s => s * completedCosZeta a s) (𝓝[!=] 0) (𝓝 (-1)) := by
  have h1 : Tendsto (fun s : Complex => s * _) (𝓝[!=] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  refine (h1.comp <| zero_div (2 : Complex) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s => ?_)
  simp [completedCosZeta, div_mul_eq_mul_div, mul_div_assoc]

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/--
lemma `hasSum_int_completedCosZeta` / 引理 `hasSum_int_completedCosZeta`

English:
lemma hasSum_int_completedCosZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  let c (n : Int) : Complex := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : Int => if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n => ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div]
  simp only [← Int.cast_eq_zero (α := Real)] at hF
  rw [show completedCosZeta a s = mellin (fun t => (cosKernel a t - 1 : Complex) / 2) (s / 2) by
    rw [mellin_div_const]; rw [completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 <= |(i : Real)| ^ s.re), div_right_comm, le_rfl]
  · simp [c, ← Int.cast_abs, div_right_comm, mul_div_assoc]

中文:
引理 hasSum_int_completedCosZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  let c (n : Int) : Complex := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : Int => if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n => ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div]
  simp only [← Int.cast_eq_zero (α := Real)] at hF
  rw [show completedCosZeta a s = mellin (fun t => (cosKernel a t - 1 : Complex) / 2) (s / 2) by
    rw [mellin_div_const]; rw [completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 <= |(i : Real)| ^ s.re), div_right_comm, le_rfl]
  · simp [c, ← Int.cast_abs, div_right_comm, mul_div_assoc]

Depends on / 依赖: HasSum, Int.cast_eq_zero, cast_eq_zero, completedCosZeta, congr_fun, cosKernel, div_const, div_mul_eq_mul_div, mellin, mellin_div_const, split_ifs
-/
lemma hasSum_int_completedCosZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => GammaReal s * cexp (2 * π * I * a * n) / (↑|n| : Complex) ^ s / 2)
    (completedCosZeta a s) := by
  let c (n : Int) : Complex := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : Int => if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n => ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div]
  simp only [← Int.cast_eq_zero (α := Real)] at hF
  rw [show completedCosZeta a s = mellin (fun t => (cosKernel a t - 1 : Complex) / 2) (s / 2) by
    rw [mellin_div_const]; rw [completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 <= |(i : Real)| ^ s.re), div_right_comm, le_rfl]
  · simp [c, ← Int.cast_abs, div_right_comm, mul_div_assoc]

/--
lemma `hasSum_nat_completedCosZeta` / 引理 `hasSum_nat_completedCosZeta`

English:
lemma hasSum_nat_completedCosZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  have aux : ((|0| : Int) : Complex) ^ s = 0 := by
    rw [abs_zero]; rw [Int.cast_zero]; rw [zero_cpow (ne_zero_of_one_lt_re hs)]
  have hint := (hasSum_int_completedCosZeta a hs).nat_add_neg
  rw [aux]; rw [div_zero]; rw [zero_div]; rw [add_zero] at hint
  refine hint.congr_fun fun n => ?_
  split_ifs with h
  · simp only [h, Nat.cast_zero, aux, div_zero, zero_div, neg_zero, zero_add]
  · simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
      show 2 * π * a * n * I = 2 * π * I * a * n by ring, neg_mul, mul_div_assoc,
      div_right_comm _ (2 : Complex), Int.cast_natCast, Nat.abs_cast, Int.cast_neg, mul_neg, abs_neg, ←
      mul_add, ← add_div]

中文:
引理 hasSum_nat_completedCosZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  have aux : ((|0| : Int) : Complex) ^ s = 0 := by
    rw [abs_zero]; rw [Int.cast_zero]; rw [zero_cpow (ne_zero_of_one_lt_re hs)]
  have hint := (hasSum_int_completedCosZeta a hs).nat_add_neg
  rw [aux]; rw [div_zero]; rw [zero_div]; rw [add_zero] at hint
  refine hint.congr_fun fun n => ?_
  split_ifs with h
  · simp only [h, Nat.cast_zero, aux, div_zero, zero_div, neg_zero, zero_add]
  · simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
      show 2 * π * a * n * I = 2 * π * I * a * n by ring, neg_mul, mul_div_assoc,
      div_right_comm _ (2 : Complex), Int.cast_natCast, Nat.abs_cast, Int.cast_neg, mul_neg, abs_neg, ←
      mul_add, ← add_div]

Depends on / 依赖: Complex.cos, Int.cast_zero, Nat.cast_zero, abs_zero, add_zero, cast_zero, congr_fun, div_zero, hasSum_int_completedCosZeta, hint.congr_fun, nat_add_neg, ne_zero_of_one_lt_re, neg_zero, ofReal_cos, ofReal_mul, ofReal_natCast, ofReal_ofNat, split_ifs, zero_add, zero_cpow
-/
lemma hasSum_nat_completedCosZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => if n = 0 then 0 else GammaReal s * Real.cos (2 * π * a * n) / (n : Complex) ^ s)
    (completedCosZeta a s) := by
  have aux : ((|0| : Int) : Complex) ^ s = 0 := by
    rw [abs_zero]; rw [Int.cast_zero]; rw [zero_cpow (ne_zero_of_one_lt_re hs)]
  have hint := (hasSum_int_completedCosZeta a hs).nat_add_neg
  rw [aux]; rw [div_zero]; rw [zero_div]; rw [add_zero] at hint
  refine hint.congr_fun fun n => ?_
  split_ifs with h
  · simp only [h, Nat.cast_zero, aux, div_zero, zero_div, neg_zero, zero_add]
  · simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
      show 2 * π * a * n * I = 2 * π * I * a * n by ring, neg_mul, mul_div_assoc,
      div_right_comm _ (2 : Complex), Int.cast_natCast, Nat.abs_cast, Int.cast_neg, mul_neg, abs_neg, ←
      mul_add, ← add_div]

/--
lemma `hasSum_int_completedHurwitzZetaEven` / 引理 `hasSum_int_completedHurwitzZetaEven`

English:
lemma hasSum_int_completedHurwitzZetaEven
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  have hF (t : Real) (ht : 0 < t) : HasSum (fun n : Int => if n + a = 0 then 0
      else (1 / 2 : Complex) * rexp (-π * (n + a) ^ 2 * t))
      ((evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n => ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div]
  rw [show completedHurwitzZetaEven a s = mellin (fun t => ((evenKernel (↑a) t : Complex) -
        ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) (s / 2) by
    simp_rw [mellin_div_const]; rw [apply_ite ofReal]; rw [ofReal_one]; rw [ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  · rw [mul_one_div, div_right_comm]

中文:
引理 hasSum_int_completedHurwitzZetaEven
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  have hF (t : Real) (ht : 0 < t) : HasSum (fun n : Int => if n + a = 0 then 0
      else (1 / 2 : Complex) * rexp (-π * (n + a) ^ 2 * t))
      ((evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n => ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div]
  rw [show completedHurwitzZetaEven a s = mellin (fun t => ((evenKernel (↑a) t : Complex) -
        ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) (s / 2) by
    simp_rw [mellin_div_const]; rw [apply_ite ofReal]; rw [ofReal_one]; rw [ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  · rw [mul_one_div, div_right_comm]

Depends on / 依赖: HasSum, UnitAddC, UnitAddCircle, completedHurwitzZetaEven, congr_fun, div_const, evenKernel, hasSum_ofReal, hasSum_ofReal.mpr, mellin, mul_comm, mul_one_div, ofReal_sub, ofReal_zero, split_ifs, zero_div
-/
lemma hasSum_int_completedHurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => GammaReal s / (↑|n + a| : Complex) ^ s / 2) (completedHurwitzZetaEven a s) := by
  have hF (t : Real) (ht : 0 < t) : HasSum (fun n : Int => if n + a = 0 then 0
      else (1 / 2 : Complex) * rexp (-π * (n + a) ^ 2 * t))
      ((evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n => ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div]
  rw [show completedHurwitzZetaEven a s = mellin (fun t => ((evenKernel (↑a) t : Complex) -
        ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : Real)) / 2) (s / 2) by
    simp_rw [mellin_div_const]; rw [apply_ite ofReal]; rw [ofReal_one]; rw [ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n => ?_
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  · rw [mul_one_div, div_right_comm]

/-!
## The un-completed even Hurwitz zeta
-/

/--
lemma `differentiableAt_update_of_residue` / 引理 `differentiableAt_update_of_residue`

English:
lemma differentiableAt_update_of_residue
  proof: by
  have claim (t) (ht : t != 0) (ht' : t != 1) : DifferentiableAt Complex (fun u : Complex => Λ u / GammaReal u) t :=
    (hf t ht ht').mul differentiable_GammaReal_inv.differentiableAt
  have claim2 : Tendsto (fun s : Complex => Λ s / GammaReal s) (𝓝[!=] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div GammaReal_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s != 0)
    rw [Pi.div_apply]; rw [← div_div]; rw [mul_div_cancel_left₀ _ hs]
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    simp_rw [← claim2.limUnder_eq]
    have S_nhds : {(1 : Complex)}ᶜ in 𝓝 (0 : Complex) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht => (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [GammaReal, zero_div, div_zero, Complex.Gamma_zero, mul_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto claim2 <| one_ne_zero' Complex).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x => by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' => (hx <| inv_eq_zero.mp hx').elim

中文:
引理 differentiableAt_update_of_residue
  证明: by
  have claim (t) (ht : t != 0) (ht' : t != 1) : DifferentiableAt Complex (fun u : Complex => Λ u / GammaReal u) t :=
    (hf t ht ht').mul differentiable_GammaReal_inv.differentiableAt
  have claim2 : Tendsto (fun s : Complex => Λ s / GammaReal s) (𝓝[!=] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div GammaReal_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s != 0)
    rw [Pi.div_apply]; rw [← div_div]; rw [mul_div_cancel_left₀ _ hs]
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    simp_rw [← claim2.limUnder_eq]
    have S_nhds : {(1 : Complex)}ᶜ in 𝓝 (0 : Complex) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht => (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [GammaReal, zero_div, div_zero, Complex.Gamma_zero, mul_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto claim2 <| one_ne_zero' Complex).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x => by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' => (hx <| inv_eq_zero.mp hx').elim

Depends on / 依赖: DifferentiableAt, GammaReal, GammaReal_residue_zero, Pi.div_apply, Tendsto, Tendsto.congr, claim2, differentiableAt, differentiable_GammaReal_inv, differentiable_GammaReal_inv.differentiableAt, div_apply, div_div, filter_upwards, h_lim, h_lim.div, ne_or_eq, self_mem_nhdsWithin, two_ne_zero
-/
lemma differentiableAt_update_of_residue
    {Λ : Complex -> Complex} (hf : forall (s : Complex) (_ : s != 0) (_ : s != 1), DifferentiableAt Complex Λ s)
    {L : Complex} (h_lim : Tendsto (fun s => s * Λ s) (𝓝[!=] 0) (𝓝 L)) (s : Complex) (hs' : s != 1) :
    DifferentiableAt Complex (Function.update (fun s => Λ s / GammaReal s) 0 (L / 2)) s := by
  have claim (t) (ht : t != 0) (ht' : t != 1) : DifferentiableAt Complex (fun u : Complex => Λ u / GammaReal u) t :=
    (hf t ht ht').mul differentiable_GammaReal_inv.differentiableAt
  have claim2 : Tendsto (fun s : Complex => Λ s / GammaReal s) (𝓝[!=] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div GammaReal_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s != 0)
    rw [Pi.div_apply]; rw [← div_div]; rw [mul_div_cancel_left₀ _ hs]
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    simp_rw [← claim2.limUnder_eq]
    have S_nhds : {(1 : Complex)}ᶜ in 𝓝 (0 : Complex) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht => (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [GammaReal, zero_div, div_zero, Complex.Gamma_zero, mul_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto claim2 <| one_ne_zero' Complex).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x => by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' => (hx <| inv_eq_zero.mp hx').elim

/--
Definition of `hurwitzZetaEven` / `hurwitzZetaEven` 的定义

English:
definition hurwitzZetaEven
  signature: (a : UnitAddCircle)
  body: Function.update (fun s => completedHurwitzZetaEven a s / GammaReal s)
  0 (if a = 0 then -1 / 2 else 0)

中文:
定义 hurwitzZetaEven
  签名: (a : UnitAddCircle)
  定义体: Function.update (fun s => completedHurwitzZetaEven a s / GammaReal s)
  0 (if a = 0 then -1 / 2 else 0)

Depends on / 依赖: Function, Function.update, GammaReal, completedHurwitzZetaEven, update
-/
noncomputable def hurwitzZetaEven (a : UnitAddCircle) :=
  Function.update (fun s => completedHurwitzZetaEven a s / GammaReal s)
  0 (if a = 0 then -1 / 2 else 0)

/--
lemma `hurwitzZetaEven_def_of_ne_or_ne` / 引理 `hurwitzZetaEven_def_of_ne_or_ne`

English:
lemma hurwitzZetaEven_def_of_ne_or_ne
  given: {a : UnitAddCircle} {s : Complex} (h : a != 0 ∨ s != 0)
  proof: by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h' | rfl
  · rw [Function.update_of_ne h']
  · simpa [GammaReal] using h

中文:
引理 hurwitzZetaEven_def_of_ne_or_ne
  条件: {a : UnitAddCircle} {s : 复形} (h : a != 0 ∨ s != 0)
  证明: by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h' | rfl
  · rw [Function.update_of_ne h']
  · simpa [GammaReal] using h

Depends on / 依赖: Function, Function.update_of_ne, GammaReal, hurwitzZetaEven, ne_or_eq, update_of_ne
-/
lemma hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : Complex} (h : a != 0 ∨ s != 0) :
    hurwitzZetaEven a s = completedHurwitzZetaEven a s / GammaReal s := by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h' | rfl
  · rw [Function.update_of_ne h']
  · simpa [GammaReal] using h

/--
lemma `hurwitzZetaEven_apply_zero` / 引理 `hurwitzZetaEven_apply_zero`

English:
lemma hurwitzZetaEven_apply_zero
  given: (a : UnitAddCircle)
  proof: Function.update_self ..

中文:
引理 hurwitzZetaEven_apply_zero
  条件: (a : UnitAddCircle)
  证明: Function.update_self ..

Depends on / 依赖: Function, Function.update_self, update_self
-/
lemma hurwitzZetaEven_apply_zero (a : UnitAddCircle) :
    hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0 :=
  Function.update_self ..

/--
lemma `hurwitzZetaEven_neg` / 引理 `hurwitzZetaEven_neg`

English:
lemma hurwitzZetaEven_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [hurwitzZetaEven]

中文:
引理 hurwitzZetaEven_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [hurwitzZetaEven]

Depends on / 依赖: hurwitzZetaEven
-/
lemma hurwitzZetaEven_neg (a : UnitAddCircle) (s : Complex) :
    hurwitzZetaEven (-a) s = hurwitzZetaEven a s := by
  simp [hurwitzZetaEven]

/--
theorem `hurwitzZetaEven_neg_two_mul_nat_add_one` / 定理 `hurwitzZetaEven_neg_two_mul_nat_add_one`

English:
theorem hurwitzZetaEven_neg_two_mul_nat_add_one
  given: (a : UnitAddCircle) (n : Nat)
  proof: by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by simp⟩]; rw [div_zero]

中文:
定理 hurwitzZetaEven_neg_two_mul_nat_add_one
  条件: (a : UnitAddCircle) (n : 自然数)
  证明: by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by simp⟩]; rw [div_zero]

Depends on / 依赖: Function, Function.update_of_ne, GammaReal_eq_zero_iff, GammaReal_eq_zero_iff.mpr, Nat.cast_add_one_ne_zero, cast_add_one_ne_zero, div_zero, hurwitzZetaEven, mul_ne_zero, neg_ne_zero, neg_ne_zero.mpr, two_ne_zero, update_of_ne
-/
theorem hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) :
    hurwitzZetaEven a (-2 * (n + 1)) = 0 := by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by simp⟩]; rw [div_zero]

/--
lemma `differentiableAt_hurwitzZetaEven` / 引理 `differentiableAt_hurwitzZetaEven`

English:
lemma differentiableAt_hurwitzZetaEven
  given: (a : UnitAddCircle) {s : Complex} (hs' : s != 1)
  proof: by
  have := differentiableAt_update_of_residue
    (fun t ht ht' => differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this

中文:
引理 differentiableAt_hurwitzZetaEven
  条件: (a : UnitAddCircle) {s : 复形} (hs' : s != 1)
  证明: by
  have := differentiableAt_update_of_residue
    (fun t ht ht' => differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this

Depends on / 依赖: Or.inl, completedHurwitzZetaEven_residue_zero, differentiableAt_completedHurwitzZetaEven, differentiableAt_update_of_residue, div_eq_mul_inv, ite_mul, simp_rw, zero_mul
-/
lemma differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : Complex} (hs' : s != 1) :
    DifferentiableAt Complex (hurwitzZetaEven a) s := by
  have := differentiableAt_update_of_residue
    (fun t ht ht' => differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this

/--
lemma `hurwitzZetaEven_residue_one` / 引理 `hurwitzZetaEven_residue_one`

English:
lemma hurwitzZetaEven_residue_one
  given: (a : UnitAddCircle)
  proof: by
  have : Tendsto (fun s => (s - 1) * completedHurwitzZetaEven a s / GammaReal s) (𝓝[!=] 1) (𝓝 1) := by
    simpa only [GammaReal_one, inv_one, mul_one] using! (completedHurwitzZetaEven_residue_one a).mul
 (differentiable_GammaReal_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]

中文:
引理 hurwitzZetaEven_residue_one
  条件: (a : UnitAddCircle)
  证明: by
  have : Tendsto (fun s => (s - 1) * completedHurwitzZetaEven a s / GammaReal s) (𝓝[!=] 1) (𝓝 1) := by
    simpa only [GammaReal_one, inv_one, mul_one] using! (completedHurwitzZetaEven_residue_one a).mul
 (differentiable_GammaReal_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]

Depends on / 依赖: GammaReal, GammaReal_one, Or.inr, Tendsto, completedHurwitzZetaEven, completedHurwitzZetaEven_residue_one, continuous, differentiable_GammaReal_inv, differentiable_GammaReal_inv.continuous.tendsto, eventually_ne_nhdsWithin, filter_upwards, hurwitzZetaEven_def_of_ne_or_ne, inv_one, mono_left, mul_div_assoc, mul_one, nhdsWithin_le_nhds, one_ne_zero, tendsto, this.congr
-/
lemma hurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s => (s - 1) * hurwitzZetaEven a s) (𝓝[!=] 1) (𝓝 1) := by
  have : Tendsto (fun s => (s - 1) * completedHurwitzZetaEven a s / GammaReal s) (𝓝[!=] 1) (𝓝 1) := by
    simpa only [GammaReal_one, inv_one, mul_one] using! (completedHurwitzZetaEven_residue_one a).mul
 (differentiable_GammaReal_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]

/--
lemma `differentiableAt_hurwitzZetaEven_sub_one_div` / 引理 `differentiableAt_hurwitzZetaEven_sub_one_div`

English:
lemma differentiableAt_hurwitzZetaEven_sub_one_div
  given: (a : UnitAddCircle)
  proof: by
  suffices DifferentiableAt Complex
      (fun s => completedHurwitzZetaEven a s / GammaReal s - 1 / (s - 1) / GammaReal s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven]; rw [Function.update_of_ne hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (GammaReal _)]
  refine DifferentiableAt.mul ?_ differentiable_GammaReal_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_cancel, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
 (differentiableAt_const _).div differentiableAt_id one_ne_zero

中文:
引理 differentiableAt_hurwitzZetaEven_sub_one_div
  条件: (a : UnitAddCircle)
  证明: by
  suffices DifferentiableAt Complex
      (fun s => completedHurwitzZetaEven a s / GammaReal s - 1 / (s - 1) / GammaReal s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven]; rw [Function.update_of_ne hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (GammaReal _)]
  refine DifferentiableAt.mul ?_ differentiable_GammaReal_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_cancel, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
 (differentiableAt_const _).div differentiableAt_id one_ne_zero

Depends on / 依赖: DifferentiableAt, DifferentiableAt.mul, Function, Function.update_of_ne, GammaReal, add_assoc, completedHurwitzZetaEven, completedHurwitzZetaEven_eq, congr_of_eventuallyEq, differentiableAt, differentiable_GammaReal_inv, differentiable_GammaReal_inv.differentiableAt, div_eq_mul_inv, div_ne, eventually_ne_nhds, filter_upwards, hurwitzZetaEven, neg_sub, one_ne_zero, simp_rw
-/
lemma differentiableAt_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt Complex (fun s => hurwitzZetaEven a s - 1 / (s - 1) / GammaReal s) 1 := by
  suffices DifferentiableAt Complex
      (fun s => completedHurwitzZetaEven a s / GammaReal s - 1 / (s - 1) / GammaReal s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven]; rw [Function.update_of_ne hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (GammaReal _)]
  refine DifferentiableAt.mul ?_ differentiable_GammaReal_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_cancel, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
 (differentiableAt_const _).div differentiableAt_id one_ne_zero

/--
lemma `tendsto_hurwitzZetaEven_sub_one_div_nhds_one` / 引理 `tendsto_hurwitzZetaEven_sub_one_div_nhds_one`

English:
lemma tendsto_hurwitzZetaEven_sub_one_div_nhds_one
  given: (a : UnitAddCircle)
  proof: by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto

中文:
引理 tendsto_hurwitzZetaEven_sub_one_div_nhds_one
  条件: (a : UnitAddCircle)
  证明: by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto

Depends on / 依赖: continuousAt, continuousAt.tendsto, differentiableAt_hurwitzZetaEven_sub_one_div, tendsto
-/
lemma tendsto_hurwitzZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s => hurwitzZetaEven a s - 1 / (s - 1) / GammaReal s) (𝓝 1)
    (𝓝 (hurwitzZetaEven a 1)) := by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto

/--
lemma `differentiable_hurwitzZetaEven_sub_hurwitzZetaEven` / 引理 `differentiable_hurwitzZetaEven_sub_hurwitzZetaEven`

English:
lemma differentiable_hurwitzZetaEven_sub_hurwitzZetaEven
  given: (a b : UnitAddCircle)
  proof: by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert!
    (differentiableAt_hurwitzZetaEven_sub_one_div a).fun_sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using
    2 with s
    abel

中文:
引理 differentiable_hurwitzZetaEven_sub_hurwitzZetaEven
  条件: (a b : UnitAddCircle)
  证明: by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert!
    (differentiableAt_hurwitzZetaEven_sub_one_div a).fun_sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using
    2 with s
    abel

Depends on / 依赖: convert, differentiableAt_hurwitzZetaEven, differentiableAt_hurwitzZetaEven_sub_one_div, fun_sub, ne_or_eq
-/
lemma differentiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) :
    Differentiable Complex (fun s => hurwitzZetaEven a s - hurwitzZetaEven b s) := by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert!
    (differentiableAt_hurwitzZetaEven_sub_one_div a).fun_sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using
    2 with s
    abel

/--
lemma `hasSum_int_hurwitzZetaEven` / 引理 `hasSum_int_hurwitzZetaEven`

English:
lemma hasSum_int_hurwitzZetaEven
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  rw [hurwitzZetaEven]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  have := (hasSum_int_completedHurwitzZetaEven a hs).div_const (GammaReal s)
  exact this.congr_fun fun n => by simp only [div_right_comm _ _ (GammaReal _),
    div_self (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

中文:
引理 hasSum_int_hurwitzZetaEven
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  rw [hurwitzZetaEven]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  have := (hasSum_int_completedHurwitzZetaEven a hs).div_const (GammaReal s)
  exact this.congr_fun fun n => by simp only [div_right_comm _ _ (GammaReal _),
    div_self (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

Depends on / 依赖: Function, Function.update_of_ne, GammaReal, GammaReal_ne_zero_of_re_pos, congr_fun, div_const, div_right_comm, div_self, hasSum_int_completedHurwitzZetaEven, hurwitzZetaEven, ne_zero_of_one_lt_re, this.congr_fun, update_of_ne, zero_lt_one, zero_lt_one.trans
-/
lemma hasSum_int_hurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => 1 / (↑|n + a| : Complex) ^ s / 2) (hurwitzZetaEven a s) := by
  rw [hurwitzZetaEven]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  have := (hasSum_int_completedHurwitzZetaEven a hs).div_const (GammaReal s)
  exact this.congr_fun fun n => by simp only [div_right_comm _ _ (GammaReal _),
    div_self (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/--
lemma `hasSum_nat_hurwitzZetaEven` / 引理 `hasSum_nat_hurwitzZetaEven`

English:
lemma hasSum_nat_hurwitzZetaEven
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  refine (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  simp [← abs_neg (n + 1 - a), -neg_sub, neg_sub', add_div]

中文:
引理 hasSum_nat_hurwitzZetaEven
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  refine (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  simp [← abs_neg (n + 1 - a), -neg_sub, neg_sub', add_div]

Depends on / 依赖: abs_neg, add_div, congr_fun, hasSum_int_hurwitzZetaEven, nat_add_neg_add_one, nat_add_neg_add_one.congr_fun, neg_sub
-/
lemma hasSum_nat_hurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => (1 / (↑|n + a| : Complex) ^ s + 1 / (↑|n + 1 - a| : Complex) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  simp [← abs_neg (n + 1 - a), -neg_sub, neg_sub', add_div]

/--
lemma `hasSum_nat_hurwitzZetaEven_of_mem_Icc` / 引理 `hasSum_nat_hurwitzZetaEven_of_mem_Icc`

English:
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc
  given: {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s)
  proof: by
  refine (hasSum_nat_hurwitzZetaEven a hs).congr_fun fun n => ?_
  congr 2 <;>
  rw [abs_of_nonneg (by linarith [ha.1]; rw [ha.2])] <;>
  simp

中文:
引理 hasSum_nat_hurwitzZetaEven_of_mem_Icc
  条件: {a : 实数} (ha : a in 闭区间 0 1) {s : 复形} (hs : 1 < re s)
  证明: by
  refine (hasSum_nat_hurwitzZetaEven a hs).congr_fun fun n => ?_
  congr 2 <;>
  rw [abs_of_nonneg (by linarith [ha.1]; rw [ha.2])] <;>
  simp

Depends on / 依赖: abs_of_nonneg, congr_fun, hasSum_nat_hurwitzZetaEven
-/
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => (1 / (n + a : Complex) ^ s + 1 / (n + 1 - a : Complex) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_nat_hurwitzZetaEven a hs).congr_fun fun n => ?_
  congr 2 <;>
  rw [abs_of_nonneg (by linarith [ha.1]; rw [ha.2])] <;>
  simp

/-!
## The un-completed cosine zeta
-/

/--
Definition of `cosZeta` / `cosZeta` 的定义

English:
definition cosZeta
  signature: (a : UnitAddCircle)
  body: Function.update (fun s : Complex => completedCosZeta a s / GammaReal s) 0 (-1 / 2)

中文:
定义 cosZeta
  签名: (a : UnitAddCircle)
  定义体: Function.update (fun s : Complex => completedCosZeta a s / GammaReal s) 0 (-1 / 2)

Depends on / 依赖: Function, Function.update, GammaReal, completedCosZeta, update
-/
noncomputable def cosZeta (a : UnitAddCircle) :=
  Function.update (fun s : Complex => completedCosZeta a s / GammaReal s) 0 (-1 / 2)

/--
lemma `cosZeta_apply_zero` / 引理 `cosZeta_apply_zero`

English:
lemma cosZeta_apply_zero
  given: (a : UnitAddCircle)
  statement: cosZeta a 0 = -1 / 2
  proof: Function.update_self ..

中文:
引理 cosZeta_apply_zero
  条件: (a : UnitAddCircle)
  结论: cosZeta a 0 = -1 / 2
  证明: Function.update_self ..

Depends on / 依赖: Function, Function.update_self, update_self
-/
lemma cosZeta_apply_zero (a : UnitAddCircle) : cosZeta a 0 = -1 / 2 :=
  Function.update_self ..

/--
lemma `cosZeta_neg` / 引理 `cosZeta_neg`

English:
lemma cosZeta_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [cosZeta]

中文:
引理 cosZeta_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [cosZeta]

Depends on / 依赖: cosZeta
-/
lemma cosZeta_neg (a : UnitAddCircle) (s : Complex) :
    cosZeta (-a) s = cosZeta a s := by
  simp [cosZeta]

/--
theorem `cosZeta_neg_two_mul_nat_add_one` / 定理 `cosZeta_neg_two_mul_nat_add_one`

English:
theorem cosZeta_neg_two_mul_nat_add_one
  given: (a : UnitAddCircle) (n : Nat)
  proof: by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by rw [neg_mul]; rw [Nat.cast_add_one]⟩, div_zero]

中文:
定理 cosZeta_neg_two_mul_nat_add_one
  条件: (a : UnitAddCircle) (n : 自然数)
  证明: by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by rw [neg_mul]; rw [Nat.cast_add_one]⟩, div_zero]

Depends on / 依赖: Function, Function.update_of_ne, GammaReal_eq_zero_iff, GammaReal_eq_zero_iff.mpr, Nat.cast_add_one, Nat.cast_add_one_ne_zero, cast_add_one, cast_add_one_ne_zero, cosZeta, div_zero, mul_ne_zero, neg_mul, neg_ne_zero, neg_ne_zero.mpr, two_ne_zero, update_of_ne
-/
theorem cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) :
    cosZeta a (-2 * (n + 1)) = 0 := by
  have : (-2 : Complex) * (n + 1) != 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta]; rw [Function.update_of_ne this]; rw [GammaReal_eq_zero_iff.mpr ⟨n + 1]; rw [by rw [neg_mul]; rw [Nat.cast_add_one]⟩, div_zero]

/--
lemma `differentiableAt_cosZeta` / 引理 `differentiableAt_cosZeta`

English:
lemma differentiableAt_cosZeta
  given: (a : UnitAddCircle) {s : Complex} (hs' : s != 1 ∨ a != 0)
  proof: by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' =>
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').fun_mul
      (differentiable_GammaReal_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    rw [cosZeta]; rw [Function.update_of_ne hx]; rw [div_eq_mul_inv]

中文:
引理 differentiableAt_cosZeta
  条件: (a : UnitAddCircle) {s : 复形} (hs' : s != 1 ∨ a != 0)
  证明: by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' =>
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').fun_mul
      (differentiable_GammaReal_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    rw [cosZeta]; rw [Function.update_of_ne hx]; rw [div_eq_mul_inv]

Depends on / 依赖: Function, Function.update_of_ne, Or.inl, completedCosZeta_residue_zero, congr_of_eventuallyEq, cosZeta, differentiableAt, differentiableAt_completedCosZeta, differentiableAt_update_of_residue, differentiable_GammaReal_inv, differentiable_GammaReal_inv.differentiableAt, div_eq_mul_inv, filter_upwards, fun_mul, isOpen_compl_singleton, isOpen_compl_singleton.mem_nhds, mem_nhds, ne_or_eq, one_ne_zero, update_of_ne
-/
lemma differentiableAt_cosZeta (a : UnitAddCircle) {s : Complex} (hs' : s != 1 ∨ a != 0) :
    DifferentiableAt Complex (cosZeta a) s := by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' =>
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').fun_mul
      (differentiable_GammaReal_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    rw [cosZeta]; rw [Function.update_of_ne hx]; rw [div_eq_mul_inv]

/--
lemma `differentiable_cosZeta_of_ne_zero` / 引理 `differentiable_cosZeta_of_ne_zero`

English:
lemma differentiable_cosZeta_of_ne_zero
  given: {a : UnitAddCircle} (ha : a != 0)
  proof: fun _ => differentiableAt_cosZeta a (Or.inr ha)

中文:
引理 differentiable_cosZeta_of_ne_zero
  条件: {a : UnitAddCircle} (ha : a != 0)
  证明: fun _ => differentiableAt_cosZeta a (Or.inr ha)

Depends on / 依赖: Or.inr, differentiableAt_cosZeta
-/
lemma differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a != 0) :
    Differentiable Complex (cosZeta a) :=
  fun _ => differentiableAt_cosZeta a (Or.inr ha)

/--
lemma `hasSum_int_cosZeta` / 引理 `hasSum_int_cosZeta`

English:
lemma hasSum_int_cosZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  rw [cosZeta]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  refine ((hasSum_int_completedCosZeta a hs).div_const (GammaReal s)).congr_fun fun n => ?_
  rw [mul_div_assoc _ (cexp _)]; rw [div_right_comm _ (2 : Complex)]; rw [mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

中文:
引理 hasSum_int_cosZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  rw [cosZeta]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  refine ((hasSum_int_completedCosZeta a hs).div_const (GammaReal s)).congr_fun fun n => ?_
  rw [mul_div_assoc _ (cexp _)]; rw [div_right_comm _ (2 : Complex)]; rw [mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

Depends on / 依赖: Function, Function.update_of_ne, GammaReal, GammaReal_ne_zero_of_re_pos, congr_fun, cosZeta, div_const, div_right_comm, hasSum_int_completedCosZeta, mul_div_assoc, ne_zero_of_one_lt_re, update_of_ne, zero_lt_one, zero_lt_one.trans
-/
lemma hasSum_int_cosZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (cosZeta a s) := by
  rw [cosZeta]; rw [Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  refine ((hasSum_int_completedCosZeta a hs).div_const (GammaReal s)).congr_fun fun n => ?_
  rw [mul_div_assoc _ (cexp _)]; rw [div_right_comm _ (2 : Complex)]; rw [mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/--
lemma `hasSum_nat_cosZeta` / 引理 `hasSum_nat_cosZeta`

English:
lemma hasSum_nat_cosZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  have := (hasSum_int_cosZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero, Int.cast_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero, ← add_div,
    div_right_comm _ _ (2 : Complex)] at this
  simp_rw [push_cast, Complex.cos, neg_mul]
  exact this.congr_fun fun n => by rw [show 2 * π * a * n * I = 2 * π * I * a * n by ring]

中文:
引理 hasSum_nat_cosZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  have := (hasSum_int_cosZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero, Int.cast_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero, ← add_div,
    div_right_comm _ _ (2 : Complex)] at this
  simp_rw [push_cast, Complex.cos, neg_mul]
  exact this.congr_fun fun n => by rw [show 2 * π * a * n * I = 2 * π * I * a * n by ring]

Depends on / 依赖: Complex.cos, Int.cast_natCast, Int.cast_neg, Int.cast_zero, Nat.abs_cast, abs_cast, abs_neg, abs_zero, add_div, add_zero, cast_natCast, cast_neg, cast_zero, congr_fun, div_right_comm, div_zero, hasSum_int_cosZeta, mul_neg, nat_add_neg, ne_zero_of_one_lt_re
-/
lemma hasSum_nat_cosZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => Real.cos (2 * π * a * n) / (n : Complex) ^ s) (cosZeta a s) := by
  have := (hasSum_int_cosZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero, Int.cast_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero, ← add_div,
    div_right_comm _ _ (2 : Complex)] at this
  simp_rw [push_cast, Complex.cos, neg_mul]
  exact this.congr_fun fun n => by rw [show 2 * π * a * n * I = 2 * π * I * a * n by ring]

/--
lemma `LSeriesHasSum_cos` / 引理 `LSeriesHasSum_cos`

English:
lemma LSeriesHasSum_cos
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: (hasSum_nat_cosZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

中文:
引理 LSeriesHasSum_cos
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: (hasSum_nat_cosZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

Depends on / 依赖: LSeries, LSeries.term_of_ne_zero, congr_fun, hasSum_nat_cosZeta, ne_zero_of_one_lt_re, term_of_ne_zero
-/
lemma LSeriesHasSum_cos (a : Real) {s : Complex} (hs : 1 < re s) :
    LSeriesHasSum (Real.cos <| 2 * π * a * ·) s (cosZeta a s) :=
  (hasSum_nat_cosZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/-!
## Functional equations for the un-completed zetas
-/

/--
lemma `hurwitzZetaEven_one_sub` / 引理 `hurwitzZetaEven_one_sub`

English:
lemma hurwitzZetaEven_one_sub
  statement: (a : UnitAddCircle) {s : Complex}
  proof: by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this]; rw [completedHurwitzZetaEven_one_sub]; rw [inv_GammaReal_one_sub hs]; rw [cosZeta]; rw [Function.update_of_ne (by simpa using hs 0)]; rw [← GammaComplex]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

中文:
引理 hurwitzZetaEven_one_sub
  结论: (a : UnitAddCircle) {s : 复形}
  证明: by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this]; rw [completedHurwitzZetaEven_one_sub]; rw [inv_GammaReal_one_sub hs]; rw [cosZeta]; rw [Function.update_of_ne (by simpa using hs 0)]; rw [← GammaComplex]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

Depends on / 依赖: Function, Function.update_of_ne, GammaComplex, GammaReal, completedHurwitzZetaEven, completedHurwitzZetaEven_one_sub, cosZeta, div_eq_mul_inv, eq_comm, generalize, hurwitzZetaEven, hurwitzZetaEven_def_of_ne_or_ne, inv_GammaReal_one_sub, ring_nf, speeds, sub_eq_zero, update_of_ne
-/
lemma hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : Complex}
    (hs : forall (n : Nat), s != -n) (hs' : a != 0 ∨ s != 1) :
    hurwitzZetaEven a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * cosZeta a s := by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this]; rw [completedHurwitzZetaEven_one_sub]; rw [inv_GammaReal_one_sub hs]; rw [cosZeta]; rw [Function.update_of_ne (by simpa using hs 0)]; rw [← GammaComplex]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

/--
lemma `cosZeta_one_sub` / 引理 `cosZeta_one_sub`

English:
lemma cosZeta_one_sub
  given: (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != 1 - n)
  proof: by
  rw [← GammaComplex]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [cosZeta]; rw [Function.update_of_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this]; rw [completedCosZeta_one_sub]; rw [inv_GammaReal_one_sub (fun n => by simpa using hs (n + 1))]; rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1))]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

中文:
引理 cosZeta_one_sub
  条件: (a : UnitAddCircle) {s : 复形} (hs : 对任意 (n : 自然数), s != 1 - n)
  证明: by
  rw [← GammaComplex]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [cosZeta]; rw [Function.update_of_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this]; rw [completedCosZeta_one_sub]; rw [inv_GammaReal_one_sub (fun n => by simpa using hs (n + 1))]; rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1))]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

Depends on / 依赖: Function, Function.update_of_ne, GammaComplex, GammaReal, Or.inr, completedCosZeta, completedCosZeta_one_sub, cosZeta, div_eq_mul_inv, generalize, hurwitzZetaEven_def_of_ne_or_ne, inv_GammaReal_one_sub, ring_nf, speeds, sub_eq_zero, update_of_ne
-/
lemma cosZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != 1 - n) :
    cosZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * hurwitzZetaEven a s := by
  rw [← GammaComplex]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (GammaReal (1 - s))⁻¹ := by
    rw [cosZeta]; rw [Function.update_of_ne]; rw [div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this]; rw [completedCosZeta_one_sub]; rw [inv_GammaReal_one_sub (fun n => by simpa using hs (n + 1))]; rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1))]
  generalize GammaComplex s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

end HurwitzZeta
