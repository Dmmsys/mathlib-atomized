/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of the Fourier transform

In this file we compute the Fréchet derivative of the Fourier transform of `f`, where `f` is a
function such that both `f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here the Fourier transform is
understood as an operator `(V → E) → (W → E)`, where `V` and `W` are normed `ℝ`-vector spaces
and the Fourier transform is taken with respect to a continuous `ℝ`-bilinear
pairing `L : V × W → ℝ` and a given reference measure `μ`.

We also investigate higher derivatives: Assuming that `‖v‖^n * ‖f v‖` is integrable, we show
that the Fourier transform of `f` is `C^n`.

We also study in a parallel way the Fourier transform of the derivative, which is obtained by
tensoring the Fourier transform of the original function with the bilinear form. We also get
results for iterated derivatives.

A consequence of these results is that, if a function is smooth and all its derivatives are
integrable when multiplied by `‖v‖^k`, then the same goes for its Fourier transform, with
explicit bounds.

We give specialized versions of these results on inner product spaces (where `L` is the scalar
product) and on the real line, where we express the one-dimensional derivative in more concrete
terms, as the Fourier transform of `-2πI x * f x` (or `(-2πI x)^n * f x` for higher derivatives).

## Main definitions and results

We introduce two convenience definitions:

* `VectorFourier.fourierSMulRight L f`: given `f : V → E` and `L` a bilinear pairing
  between `V` and `W`, then this is the function `fun v ↦ -(2 * π * I) (L v ⬝) • f v`,
  from `V` to `Hom (W, E)`.
  This is essentially `ContinuousLinearMap.smulRight`, up to the factor `- 2πI` designed to make
  sure that the Fourier integral of `fourierSMulRight L f` is the derivative of the Fourier
  integral of `f`.
* `VectorFourier.fourierPowSMulRight` is the higher-order analogue for higher derivatives:
  `fourierPowSMulRight L f v n` is informally `(-(2 * π * I))^n (L v ⬝)^n • f v`, in
  the space of continuous multilinear maps `W [×n]→L[ℝ] E`.

With these definitions, the statements read as follows, first in a general context
(arbitrary `L` and `μ`):

* `VectorFourier.hasFDerivAt_fourierIntegral`: the Fourier integral of `f` is differentiable, with
    derivative the Fourier integral of `fourierSMulRight L f`.
* `VectorFourier.differentiable_fourierIntegral`: the Fourier integral of `f` is differentiable.
* `VectorFourier.fderiv_fourierIntegral`: formula for the derivative of the Fourier integral of `f`.
* `VectorFourier.fourierIntegral_fderiv`: formula for the Fourier integral of the derivative of `f`.
* `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` has an explicit Taylor series up to order `N`, given by the Fourier
  integrals of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.contDiff_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` is `C^n`.
* `VectorFourier.iteratedFDeriv_fourierIntegral`: under suitable integrability conditions,
  explicit formula for the `n`-th derivative of the Fourier integral of `f`, as the Fourier
  integral of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`: explicit bounds for the `n`-th
  derivative of the Fourier integral, multiplied by a power function, in terms of corresponding
  integrals for the original function.

These statements are then specialized to the case of the usual Fourier transform on
finite-dimensional inner product spaces with their canonical Lebesgue measure (covering in
particular the case of the real line), replacing the namespace `VectorFourier` by
the namespace `Real` in the above statements.

We also give specialized versions of the one-dimensional real derivative (and iterated derivative)
in `Real.deriv_fourierIntegral` and `Real.iteratedDeriv_fourierIntegral`.
-/

@[expose] public section

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology ContDiff

-- without this local instance, Lean tries first the instance
-- `secondCountableTopologyEither_of_right` (whose priority is 100) and takes a very long time to
-- fail. Since we only use the left instance in this file, we make sure it is tried first.
attribute [local instance 101] secondCountableTopologyEither_of_left

namespace Real

/--
lemma `hasDerivAt_fourierChar` / 引理 `hasDerivAt_fourierChar`

English:
lemma hasDerivAt_fourierChar
  given: (x : Real)
  statement: HasDerivAt (𝐞 · : Real -> Complex) (2 * π * I * 𝐞 x) x
  proof: by
  have h1 (y : Real) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply]; rw [fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

中文:
引理 hasDerivAt_fourierChar
  条件: (x : 实数)
  结论: 在点处可导 (𝐞 · : 实数 -> 复形) (2 * π * I * 𝐞 x) x
  证明: by
  have h1 (y : Real) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply]; rw [fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

Depends on / 依赖: Int.cast_one, UnitAddCircle, cast_one, div_one, fourier, fourierChar_apply, fourier_coe_apply, hasDerivAt_fourier, mul_one, ofReal_one, ring_nf
-/
lemma hasDerivAt_fourierChar (x : Real) : HasDerivAt (𝐞 · : Real -> Complex) (2 * π * I * 𝐞 x) x := by
  have h1 (y : Real) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply]; rw [fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

/--
lemma `differentiable_fourierChar` / 引理 `differentiable_fourierChar`

English:
lemma differentiable_fourierChar
  statement: Differentiable Real (𝐞 · : Real -> Complex)
  proof: fun x => (Real.hasDerivAt_fourierChar x).differentiableAt

中文:
引理 differentiable_fourierChar
  结论: 可微 实数 (𝐞 · : 实数 -> 复形)
  证明: fun x => (Real.hasDerivAt_fourierChar x).differentiableAt

Depends on / 依赖: Real.hasDerivAt_fourierChar, differentiableAt, hasDerivAt_fourierChar
-/
lemma differentiable_fourierChar : Differentiable Real (𝐞 · : Real -> Complex) :=
  fun x => (Real.hasDerivAt_fourierChar x).differentiableAt

/--
lemma `deriv_fourierChar` / 引理 `deriv_fourierChar`

English:
lemma deriv_fourierChar
  given: (x : Real)
  statement: deriv (𝐞 · : Real -> Complex) x = 2 * π * I * 𝐞 x
  proof: (Real.hasDerivAt_fourierChar x).deriv

中文:
引理 deriv_fourierChar
  条件: (x : 实数)
  结论: deriv (𝐞 · : 实数 -> 复形) x = 2 * π * I * 𝐞 x
  证明: (Real.hasDerivAt_fourierChar x).deriv

Depends on / 依赖: Real.hasDerivAt_fourierChar, hasDerivAt_fourierChar
-/
lemma deriv_fourierChar (x : Real) : deriv (𝐞 · : Real -> Complex) x = 2 * π * I * 𝐞 x :=
  (Real.hasDerivAt_fourierChar x).deriv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W] (L : V ->L[Real] W ->L[Real] Real)

/--
lemma `hasFDerivAt_fourierChar_neg_bilinear_right` / 引理 `hasFDerivAt_fourierChar_neg_bilinear_right`

English:
lemma hasFDerivAt_fourierChar_neg_bilinear_right
  given: (v : V) (w : W)
  proof: by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, neg_smul, neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.toSpanSingleton_apply, real_smul, neg_inj]
  ring

中文:
引理 hasFDerivAt_fourierChar_neg_bilinear_right
  条件: (v : V) (w : W)
  证明: by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, neg_smul, neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.toSpanSingleton_apply, real_smul, neg_inj]
  ring

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_neg, ContinuousLinearMap.hasFDerivAt, ContinuousLinearMap.toSpanSingleton_apply, HasFDerivAt, comp_apply, comp_neg, convert, ha.neg, hasDerivAt_fourierChar, hasFDerivAt, hasFDerivAt.comp, neg_apply, neg_inj, neg_mul, neg_smul, ofRealCLM_apply, real_smul, smul_apply
-/
lemma hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) :
    HasFDerivAt (fun w => (𝐞 (-L v w) : Complex))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v))) w := by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, neg_smul, neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.toSpanSingleton_apply, real_smul, neg_inj]
  ring

/--
lemma `fderiv_fourierChar_neg_bilinear_right_apply` / 引理 `fderiv_fourierChar_neg_bilinear_right_apply`

English:
lemma fderiv_fourierChar_neg_bilinear_right_apply
  given: (v : V) (w y : W)
  proof: by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul, neg_smul,
    neg_apply, smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring

中文:
引理 fderiv_fourierChar_neg_bilinear_right_apply
  条件: (v : V) (w y : W)
  证明: by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul, neg_smul,
    neg_apply, smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, comp_apply, fderiv, hasFDerivAt_fourierChar_neg_bilinear_right, neg_apply, neg_inj, neg_mul, neg_smul, ofRealCLM_apply, smul_apply, smul_eq_mul
-/
lemma fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) :
    fderiv Real (fun w => (𝐞 (-L v w) : Complex)) w y = -2 * π * I * L v y * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul, neg_smul,
    neg_apply, smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring

/--
lemma `differentiable_fourierChar_neg_bilinear_right` / 引理 `differentiable_fourierChar_neg_bilinear_right`

English:
lemma differentiable_fourierChar_neg_bilinear_right
  given: (v : V)
  proof: fun w => (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt

中文:
引理 differentiable_fourierChar_neg_bilinear_right
  条件: (v : V)
  证明: fun w => (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt_fourierChar_neg_bilinear_right
-/
lemma differentiable_fourierChar_neg_bilinear_right (v : V) :
    Differentiable Real (fun w => (𝐞 (-L v w) : Complex)) :=
  fun w => (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt

/--
lemma `hasFDerivAt_fourierChar_neg_bilinear_left` / 引理 `hasFDerivAt_fourierChar_neg_bilinear_left`

English:
lemma hasFDerivAt_fourierChar_neg_bilinear_left
  given: (v : V) (w : W)
  proof: hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v

中文:
引理 hasFDerivAt_fourierChar_neg_bilinear_left
  条件: (v : V) (w : W)
  证明: hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v

Depends on / 依赖: L.flip, hasFDerivAt_fourierChar_neg_bilinear_right
-/
lemma hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) :
    HasFDerivAt (fun v => (𝐞 (-L v w) : Complex))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.flip w))) v :=
  hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v

/--
lemma `fderiv_fourierChar_neg_bilinear_left_apply` / 引理 `fderiv_fourierChar_neg_bilinear_left_apply`

English:
lemma fderiv_fourierChar_neg_bilinear_left_apply
  given: (v y : V) (w : W)
  proof: by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul, neg_smul, neg_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply,
    smul_eq_mul, neg_inj]
  ring

中文:
引理 fderiv_fourierChar_neg_bilinear_left_apply
  条件: (v y : V) (w : W)
  证明: by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul, neg_smul, neg_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply,
    smul_eq_mul, neg_inj]
  ring

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, LipschitzMul, SeminormedCommGroup, SeminormedCommGroup.to_lipschitzMul, comp_apply, fderiv, flip_apply, hasFDerivAt_fourierChar_neg_bilinear_left, neg_apply, neg_inj, neg_mul, neg_smul, ofRealCLM_apply, smul_apply, smul_eq_mul, to_lipschitzMul
-/
lemma fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) :
    fderiv Real (fun v => (𝐞 (-L v w) : Complex)) v y = -2 * π * I * L y w * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul, neg_smul, neg_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply,
    smul_eq_mul, neg_inj]
  ring

/--
lemma `differentiable_fourierChar_neg_bilinear_left` / 引理 `differentiable_fourierChar_neg_bilinear_left`

English:
lemma differentiable_fourierChar_neg_bilinear_left
  given: (w : W)
  proof: fun v => (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

中文:
引理 differentiable_fourierChar_neg_bilinear_left
  条件: (w : W)
  证明: fun v => (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

Depends on / 依赖: IsUniformGroup, SeminormedCommGroup, SeminormedCommGroup.to_isUniformGroup, differentiableAt, hasFDerivAt_fourierChar_neg_bilinear_left, to_isUniformGroup
-/
lemma differentiable_fourierChar_neg_bilinear_left (w : W) :
    Differentiable Real (fun v => (𝐞 (-L v w) : Complex)) :=
  fun v => (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

end Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W] (L : V ->L[Real] W ->L[Real] Real) (f : V -> E)

/--
Definition of `fourierSMulRight` / `fourierSMulRight` 的定义

English:
definition fourierSMulRight
  signature: (v : V)
  body: -(2 * π * I) • (L v).smulRight (f v)

中文:
定义 fourierSMulRight
  签名: (v : V)
  定义体: -(2 * π * I) • (L v).smulRight (f v)

Depends on / 依赖: IsTopologicalGroup, SeminormedCommGroup, SeminormedCommGroup.toIsTopologicalGroup, smulRight, toIsTopologicalGroup
-/
def fourierSMulRight (v : V) : (W ->L[Real] E) := -(2 * π * I) • (L v).smulRight (f v)

/--
lemma `fourierSMulRight_apply` / 引理 `fourierSMulRight_apply`

English:
lemma fourierSMulRight_apply
  given: (v : V) (w : W)
  proof: rfl

中文:
引理 fourierSMulRight_apply
  条件: (v : V) (w : W)
  证明: rfl
-/
@[simp] lemma fourierSMulRight_apply (v : V) (w : W) :
    fourierSMulRight L f v w = -(2 * π * I) • L v w • f v := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasFDerivAt_fourierChar_smul` / 引理 `hasFDerivAt_fourierChar_smul`

English:
lemma hasFDerivAt_fourierChar_smul
  given: (v : V) (w : W)
  proof: by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext w' : 1
  simp_rw [fourierSMulRight, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply]; rw [neg_apply]; rw [ContinuousLinearMap.toSpanSingleton_apply]; rw [← smul_assoc]; rw [smul_comm]; rw [← smul_assoc]; rw [real_smul]; rw [real_smul]; rw [Submonoid.smul_def]; rw [smul_eq_mul]
  push_cast
  ring_nf

中文:
引理 hasFDerivAt_fourierChar_smul
  条件: (v : V) (w : W)
  证明: by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext w' : 1
  simp_rw [fourierSMulRight, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply]; rw [neg_apply]; rw [ContinuousLinearMap.toSpanSingleton_apply]; rw [← smul_assoc]; rw [smul_comm]; rw [← smul_assoc]; rw [real_smul]; rw [real_smul]; rw [Submonoid.smul_def]; rw [smul_eq_mul]
  push_cast
  ring_nf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.hasFDerivAt, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply, HasFDerivAt, Submonoid, Submonoid.smul_def, comp_apply, convert, fourierSMulRight, ha.neg, hasDerivAt_fourierChar, hasFDerivAt, hasFDerivAt.comp, neg_apply, real_smul, simp_rw, smulRight_apply, smul_apply
-/
lemma hasFDerivAt_fourierChar_smul (v : V) (w : W) :
    HasFDerivAt (fun w' => 𝐞 (-L v w') • f v) (𝐞 (-L v w) • fourierSMulRight L f v) w := by
  have ha : HasFDerivAt (fun w' : W => L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext w' : 1
  simp_rw [fourierSMulRight, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply]; rw [neg_apply]; rw [ContinuousLinearMap.toSpanSingleton_apply]; rw [← smul_assoc]; rw [smul_comm]; rw [← smul_assoc]; rw [real_smul]; rw [real_smul]; rw [Submonoid.smul_def]; rw [smul_eq_mul]
  push_cast
  ring_nf

/--
lemma `norm_fourierSMulRight` / 引理 `norm_fourierSMulRight`

English:
lemma norm_fourierSMulRight
  given: (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (v : V)
  proof: by
  rw [fourierSMulRight]; rw [norm_smul _ (ContinuousLinearMap.smulRight (L v) (f v))]; rw [norm_neg]; rw [norm_mul]; rw [norm_mul]; rw [norm_I]; rw [mul_one]; rw [Complex.norm_of_nonneg pi_pos.le]; rw [Complex.norm_two]; rw [ContinuousLinearMap.norm_smulRight_apply]; rw [← mul_assoc]

中文:
引理 norm_fourierSMulRight
  条件: (L : V ->L[实数] W ->L[实数] 实数) (f : V -> E) (v : V)
  证明: by
  rw [fourierSMulRight]; rw [norm_smul _ (ContinuousLinearMap.smulRight (L v) (f v))]; rw [norm_neg]; rw [norm_mul]; rw [norm_mul]; rw [norm_I]; rw [mul_one]; rw [Complex.norm_of_nonneg pi_pos.le]; rw [Complex.norm_two]; rw [ContinuousLinearMap.norm_smulRight_apply]; rw [← mul_assoc]

Depends on / 依赖: Complex.norm_of_nonneg, Complex.norm_two, ContinuousLinearMap, ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.smulRight, fourierSMulRight, mul_assoc, mul_one, norm_I, norm_mul, norm_neg, norm_of_nonneg, norm_smul, norm_smulRight_apply, norm_two, pi_pos, pi_pos.le, smulRight
-/
lemma norm_fourierSMulRight (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (v : V) :
    ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := by
  rw [fourierSMulRight]; rw [norm_smul _ (ContinuousLinearMap.smulRight (L v) (f v))]; rw [norm_neg]; rw [norm_mul]; rw [norm_mul]; rw [norm_I]; rw [mul_one]; rw [Complex.norm_of_nonneg pi_pos.le]; rw [Complex.norm_two]; rw [ContinuousLinearMap.norm_smulRight_apply]; rw [← mul_assoc]

/--
lemma `norm_fourierSMulRight_le` / 引理 `norm_fourierSMulRight_le`

English:
lemma norm_fourierSMulRight_le
  given: (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (v : V)
  proof: calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ <= (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring

中文:
引理 norm_fourierSMulRight_le
  条件: (L : V ->L[实数] W ->L[实数] 实数) (f : V -> E) (v : V)
  证明: calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ <= (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring
-/
lemma norm_fourierSMulRight_le (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (v : V) :
    ‖fourierSMulRight L f v‖ <= 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ <= (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight
  proof: by
  apply AEStronglyMeasurable.fun_const_smul
  have aux0 : Continuous fun p : (W ->L[Real] Real) × E => p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL Real W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v => (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prodMk hf
  -- Elaboration without the expected type is faster here:
  exact (aux0.comp_aestronglyMeasurable aux1 :)

中文:
引理 _root_.测度论.AEStronglyMeasurable.fourierSMulRight
  证明: by
  apply AEStronglyMeasurable.fun_const_smul
  have aux0 : Continuous fun p : (W ->L[Real] Real) × E => p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL Real W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v => (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prodMk hf
  -- Elaboration without the expected type is faster here:
  exact (aux0.comp_aestronglyMeasurable aux1 :)

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.fun_const_smul, Continuous, ContinuousLinearMap, ContinuousLinearMap.smulRightL, L.continuous.aestronglyMeasurable.prodMk, aestronglyMeasurable, continuous, fun_const_smul, prodMk, smulRight, smulRightL
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight
    [SecondCountableTopologyEither V (W ->L[Real] Real)] [MeasurableSpace V] [BorelSpace V]
    {L : V ->L[Real] W ->L[Real] Real} {f : V -> E} {μ : Measure V}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v => fourierSMulRight L f v) μ := by
  apply AEStronglyMeasurable.fun_const_smul
  have aux0 : Continuous fun p : (W ->L[Real] Real) × E => p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL Real W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v => (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prodMk hf
  -- Elaboration without the expected type is faster here:
  exact (aux0.comp_aestronglyMeasurable aux1 :)

variable {f}

/--
theorem `hasFDerivAt_fourierIntegral` / 定理 `hasFDerivAt_fourierIntegral`

English:
theorem hasFDerivAt_fourierIntegral
  proof: by
  let F : W -> V -> E := fun w' v => 𝐞 (-L v w') • f v
  let F' : W -> V -> W ->L[Real] E := fun w' v => 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V -> Real := fun v => 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (fourierIntegral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W => L.toLinearMap₁₂ p.1 p.2)) w').2 hf
  have h1 : forallᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    Eventually.of_forall (fun w' => (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .fun_smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    fun_prop
  have h4 : (forallᵐ v ∂μ, forall (w' : W), w' in Metric.ball w 1 -> ‖F' w' v‖ <= B v) := by
    filter_upwards with v w' _
    rw [Circle.norm_smul _ (fourierSMulRight L f v)]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : forallᵐ v ∂μ, forall w', w' in Metric.ball w 1 -> HasFDerivAt (fun x => F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ => hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ one_pos) h1 (h0 w)
    h3 h4 h5 h6

中文:
定理 hasFDerivAt_fourier整数egral
  证明: by
  let F : W -> V -> E := fun w' v => 𝐞 (-L v w') • f v
  let F' : W -> V -> W ->L[Real] E := fun w' v => 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V -> Real := fun v => 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (fourierIntegral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W => L.toLinearMap₁₂ p.1 p.2)) w').2 hf
  have h1 : forallᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    Eventually.of_forall (fun w' => (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .fun_smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    fun_prop
  have h4 : (forallᵐ v ∂μ, forall (w' : W), w' in Metric.ball w 1 -> ‖F' w' v‖ <= B v) := by
    filter_upwards with v w' _
    rw [Circle.norm_smul _ (fourierSMulRight L f v)]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : forallᵐ v ∂μ, forall w', w' in Metric.ball w 1 -> HasFDerivAt (fun x => F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ => hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ one_pos) h1 (h0 w)
    h3 h4 h5 h6

Depends on / 依赖: AEStronglyMeasurable, Continuous, Eventually, Eventually.of_forall, Integrable, L.continuous, L.toLinearMap, aestronglyMeas, continuous_fourierChar, fourierIntegral_convergent_iff, fourierSMulRight, of_forall
-/
theorem hasFDerivAt_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f) w) w := by
  let F : W -> V -> E := fun w' v => 𝐞 (-L v w') • f v
  let F' : W -> V -> W ->L[Real] E := fun w' v => 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V -> Real := fun v => 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (fourierIntegral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W => L.toLinearMap₁₂ p.1 p.2)) w').2 hf
  have h1 : forallᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    Eventually.of_forall (fun w' => (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .fun_smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    fun_prop
  have h4 : (forallᵐ v ∂μ, forall (w' : W), w' in Metric.ball w 1 -> ‖F' w' v‖ <= B v) := by
    filter_upwards with v w' _
    rw [Circle.norm_smul _ (fourierSMulRight L f v)]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : forallᵐ v ∂μ, forall w', w' in Metric.ball w 1 -> HasFDerivAt (fun x => F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ => hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ one_pos) h1 (h0 w)
    h3 h4 h5 h6

/--
lemma `fderiv_fourierIntegral` / 引理 `fderiv_fourierIntegral`

English:
lemma fderiv_fourierIntegral
  proof: by
  ext w : 1
  exact (hasFDerivAt_fourierIntegral L hf hf' w).fderiv

中文:
引理 fderiv_fourier整数egral
  证明: by
  ext w : 1
  exact (hasFDerivAt_fourierIntegral L hf hf' w).fderiv

Depends on / 依赖: fderiv, hasFDerivAt_fourierIntegral
-/
lemma fderiv_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ) :
    fderiv Real (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f) := by
  ext w : 1
  exact (hasFDerivAt_fourierIntegral L hf hf' w).fderiv

/--
lemma `differentiable_fourierIntegral` / 引理 `differentiable_fourierIntegral`

English:
lemma differentiable_fourierIntegral
  proof: fun w => (hasFDerivAt_fourierIntegral L hf hf' w).differentiableAt

中文:
引理 differentiable_fourier整数egral
  证明: fun w => (hasFDerivAt_fourierIntegral L hf hf' w).differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt_fourierIntegral
-/
lemma differentiable_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ) :
    Differentiable Real (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) :=
  fun w => (hasFDerivAt_fourierIntegral L hf hf' w).differentiableAt

/--
theorem `fourierIntegral_fderiv` / 定理 `fourierIntegral_fderiv`

English:
theorem fourierIntegral_fderiv
  statement: [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
  proof: by
  ext w y
  let g (v : V) : Complex := 𝐞 (-L v w)
  /- First rewrite things in a simplified form, without any real change. -/
  suffices ∫ x, g x • fderiv Real f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    rw [fourierIntegral_continuousLinearMap_apply' hf']
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply, ← integral_smul, neg_smul,
      smul_neg, ← smul_smul, coe_smul, neg_neg]
  -- Key step: integrate by parts with respect to `y` to switch the derivative from `f` to `g`.
  have A x : fderiv Real g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]; rw [← integral_neg]
  · simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x => (-(2 * ↑π * I * ↑((L y) w)) • ((g x : Complex) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert! this using 2 with x
    simp only [A, neg_mul, neg_smul, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact fun _ _ => (differentiable_fourierChar_neg_bilinear_left _ _).differentiableAt
  · exact fun _ _ => h'f.differentiableAt

中文:
定理 fourier整数egral_fderiv
  结论: [可测空间 V] [Borel空间 V] [有限维 实数 V]
  证明: by
  ext w y
  let g (v : V) : Complex := 𝐞 (-L v w)
  /- First rewrite things in a simplified form, without any real change. -/
  suffices ∫ x, g x • fderiv Real f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    rw [fourierIntegral_continuousLinearMap_apply' hf']
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply, ← integral_smul, neg_smul,
      smul_neg, ← smul_smul, coe_smul, neg_neg]
  -- Key step: integrate by parts with respect to `y` to switch the derivative from `f` to `g`.
  have A x : fderiv Real g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]; rw [← integral_neg]
  · simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x => (-(2 * ↑π * I * ↑((L y) w)) • ((g x : Complex) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert! this using 2 with x
    simp only [A, neg_mul, neg_smul, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact fun _ _ => (differentiable_fourierChar_neg_bilinear_left _ _).differentiableAt
  · exact fun _ _ => h'f.differentiableAt
-/
theorem fourierIntegral_fderiv [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ]
    (hf : Integrable f μ) (h'f : Differentiable Real f) (hf' : Integrable (fderiv Real f) μ) :
    fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv Real f)
      = fourierSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  ext w y
  let g (v : V) : Complex := 𝐞 (-L v w)
  /- First rewrite things in a simplified form, without any real change. -/
  suffices ∫ x, g x • fderiv Real f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    rw [fourierIntegral_continuousLinearMap_apply' hf']
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply, ← integral_smul, neg_smul,
      smul_neg, ← smul_smul, coe_smul, neg_neg]
  -- Key step: integrate by parts with respect to `y` to switch the derivative from `f` to `g`.
  have A x : fderiv Real g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]; rw [← integral_neg]
  · simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x => (-(2 * ↑π * I * ↑((L y) w)) • ((g x : Complex) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert! this using 2 with x
    simp only [A, neg_mul, neg_smul, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact fun _ _ => (differentiable_fourierChar_neg_bilinear_left _ _).differentiableAt
  · exact fun _ _ => h'f.differentiableAt

/--
Definition of `fourierPowSMulRight` / `fourierPowSMulRight` 的定义

English:
definition fourierPowSMulRight
  signature: (f : V -> E) (v : V)
  body: fun n =>
  (- (2 * π * I)) ^ n • ((ContinuousMultilinearMap.mkPiRing Real (Fin n) (f v)).compContinuousLinearMap
  (fun _ => L v))

中文:
定义 fourierPowSMulRight
  签名: (f : V -> E) (v : V)
  定义体: fun n =>
  (- (2 * π * I)) ^ n • ((ContinuousMultilinearMap.mkPiRing Real (Fin n) (f v)).compContinuousLinearMap
  (fun _ => L v))
-/
def fourierPowSMulRight (f : V -> E) (v : V) : FormalMultilinearSeries Real W E := fun n =>
  (- (2 * π * I)) ^ n • ((ContinuousMultilinearMap.mkPiRing Real (Fin n) (f v)).compContinuousLinearMap
  (fun _ => L v))

/--
lemma `fourierPowSMulRight_apply` / 引理 `fourierPowSMulRight_apply`

English:
lemma fourierPowSMulRight_apply
  given: {f : V -> E} {v : V} {n : Nat} {m : Fin n -> W}
  proof: by
  simp [fourierPowSMulRight]

中文:
引理 fourierPowSMulRight_apply
  条件: {f : V -> E} {v : V} {n : 自然数} {m : 有限集 n -> W}
  证明: by
  simp [fourierPowSMulRight]
-/
@[simp 1100] lemma fourierPowSMulRight_apply {f : V -> E} {v : V} {n : Nat} {m : Fin n -> W} :
    fourierPowSMulRight L f v n m = (- (2 * π * I)) ^ n • (∏ i, L v (m i)) • f v := by
  simp [fourierPowSMulRight]

open ContinuousMultilinearMap

/--
lemma `fourierPowSMulRight_eq_comp` / 引理 `fourierPowSMulRight_eq_comp`

English:
lemma fourierPowSMulRight_eq_comp
  given: {f : V -> E} {v : V} {n : Nat}
  proof: rfl

@[continuity, fun_prop]

中文:
引理 fourierPowSMulRight_eq_comp
  条件: {f : V -> E} {v : V} {n : 自然数}
  证明: rfl

@[continuity, fun_prop]
-/
lemma fourierPowSMulRight_eq_comp {f : V -> E} {v : V} {n : Nat} :
    fourierPowSMulRight L f v n = (- (2 * π * I)) ^ n • smulRightL Real (fun (_ : Fin n) => W) E
      (compContinuousLinearMapLRight
        (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n) Real) (fun _ => L v)) (f v) := rfl

@[continuity, fun_prop]
/--
lemma `_root_.Continuous.fourierPowSMulRight` / 引理 `_root_.Continuous.fourierPowSMulRight`

English:
lemma _root_.Continuous.fourierPowSMulRight
  given: {f : V -> E} (hf : Continuous f) (n : Nat)
  proof: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

中文:
引理 _root_.连续.fourierPowSMulRight
  条件: {f : V -> E} (hf : 连续 f) (n : 自然数)
  证明: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

Depends on / 依赖: Continuous, Continuous.comp, Continuous.fun_const_smul, L.continuous, continuous, continuous_pi, fourierPowSMulRight_eq_comp, fun_const_smul, map_continuous, simp_rw, smulRightL
-/
lemma _root_.Continuous.fourierPowSMulRight {f : V -> E} (hf : Continuous f) (n : Nat) :
    Continuous (fun v => fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

/--
lemma `_root_.ContDiff.fourierPowSMulRight` / 引理 `_root_.ContDiff.fourierPowSMulRight`

English:
lemma _root_.ContDiff.fourierPowSMulRight
  proof: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ => L.contDiff)

中文:
引理 _root_.连续可微.fourierPowSMulRight
  证明: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ => L.contDiff)

Depends on / 依赖: ContDiff, ContDiff.const_smul, ContinuousMultilinearMap, ContinuousMultilinearMap.contDiff, L.contDiff, const_smul, contDiff, contDiff_pi, fourierPowSMulRight_eq_comp, isBoundedBilinearMap, isBoundedBilinearMap.contDiff.comp, simp_rw, smulRightL
-/
lemma _root_.ContDiff.fourierPowSMulRight
    {f : V -> E} {k : Nat∞ω} (hf : ContDiff Real k f) (n : Nat) :
    ContDiff Real k (fun v => fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ => L.contDiff)

/--
lemma `norm_fourierPowSMulRight_le` / 引理 `norm_fourierPowSMulRight_le`

English:
lemma norm_fourierPowSMulRight_le
  given: (f : V -> E) (v : V) (n : Nat)
  proof: by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [abs_of_nonneg pi_nonneg, norm_smul]
  _ <= (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

中文:
引理 norm_fourierPowSMulRight_le
  条件: (f : V -> E) (v : V) (n : 自然数)
  证明: by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [abs_of_nonneg pi_nonneg, norm_smul]
  _ <= (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, Finset, Finset.prod_mul_distrib, L.le_opNorm, abs_of_nonneg, fourierPowSMulRight, mul_pow, norm_smul, opNorm_le_bound, pi_nonneg, prod_mul_distrib
-/
lemma norm_fourierPowSMulRight_le (f : V -> E) (v : V) (n : Nat) :
    ‖fourierPowSMulRight L f v n‖ <= (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [abs_of_nonneg pi_nonneg, norm_smul]
  _ <= (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

/--
lemma `norm_iteratedFDeriv_fourierPowSMulRight` / 引理 `norm_iteratedFDeriv_fourierPowSMulRight`

English:
lemma norm_iteratedFDeriv_fourierPowSMulRight
  proof: by
  /- We write `fourierPowSMulRight L f v n` as a composition of bilinear and multilinear maps,
  thanks to `fourierPowSMulRight_eq_comp`, and then we control the iterated derivatives of these
  thanks to general bounds on derivatives of bilinear and multilinear maps. More precisely,
  `fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v`. Here,
  `(- (2 * π * I))^n` contributes `(2π)^n` to the bound. The second product is bilinear, so the
  iterated derivative is controlled as a weighted sum of those of `v ↦ ∏ i, L v (m i)` and of `f`.

  The harder part is to control the iterated derivatives of `v ↦ ∏ i, L v (m i)`. For this, one
  argues that this is multilinear in `v`, to apply general bounds for iterated derivatives of
  multilinear maps. More precisely, we write it as the composition of a multilinear map `T` (making
  the product operation) and the tuple of linear maps `v ↦ (L v ⬝, ..., L v ⬝)` -/
  simp_rw [fourierPowSMulRight_eq_comp]
  -- first step: controlling the iterated derivatives of `v ↦ ∏ i, L v (m i)`, written below
  -- as `v ↦ T (fun _ ↦ L v)`, or `T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))`.
  let T : (W ->L[Real] Real) [×n]->L[Real] (W [×n]->L[Real] Real) :=
    compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n) Real)
  have I₁ m : ‖iteratedFDeriv Real m T (fun _ => L v)‖ <=
      n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m) := by
    have : ‖T‖ <= 1 := by
      apply (norm_compContinuousLinearMapLRight_le _ _).trans
      simp only [norm_mkPiAlgebra, le_refl]
    apply (ContinuousMultilinearMap.norm_iteratedFDeriv_le _ _ _).trans
    simp only [Fintype.card_fin]
    gcongr
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun _ => ?_)
    exact ContinuousLinearMap.le_opNorm _ _
  have I₂ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      (n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m)) * ‖L‖ ^ m := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (ContinuousMultilinearMap.contDiff _)
      _ (mod_cast le_top)]
    apply (norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    · exact I₁ m
    · exact ContinuousLinearMap.norm_pi_le_of_le (fun _ => le_rfl) (norm_nonneg _)
  have I₃ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      n.descFactorial m * ‖L‖ ^ n * ‖v‖ ^ (n - m) := by
    apply (I₂ m).trans (le_of_eq _)
    rcases le_or_gt m n with hm | hm
    · rw [show ‖L‖ ^ n = ‖L‖ ^ (m + (n - m)) by rw [Nat.add_sub_cancel' hm], pow_add]
      ring
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hm, CharP.cast_eq_zero, mul_one, zero_mul]
  -- second step: factor out the `(2 * π) ^ n` factor, and cancel it on both sides.
  have A : ContDiff Real K (fun y => T (fun _ => L y)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => L.contDiff)
  rw [iteratedFDeriv_const_smul_apply' (hf := ((smulRightL Real (fun _ => W)
    E).isBoundedBilinearMap.contDiff.comp₂ (A.of_le hk) (hf.of_le hk)).contDiffAt)]; rw [norm_smul (β := V [×k]->L[Real] (W [×n]->L[Real] E))]
  simp only [mul_assoc, norm_pow, norm_neg, Complex.norm_mul, Complex.norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_of_nonneg pi_nonneg, norm_I, mul_one, smulRightL_apply, ge_iff_le]
  gcongr
  -- third step: argue that the scalar multiplication is bilinear to bound the iterated derivatives
  -- of `v ↦ (∏ i, L v (m i)) • f v` in terms of those of `v ↦ (∏ i, L v (m i))` and of `f`.
  -- The former are controlled by the first step, the latter by the assumptions.
  apply (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ A hf _
    hk ContinuousMultilinearMap.norm_smulRightL_le).trans
  calc
  ∑ i in Finset.range (k + 1),
    k.choose i * ‖iteratedFDeriv Real i (fun (y : V) => T (fun _ => L y)) v‖ *
      ‖iteratedFDeriv Real (k - i) f v‖
    <= ∑ i in Finset.range (k + 1),
      k.choose i * (n.descFactorial i * ‖L‖ ^ n * ‖v‖ ^ (n - i)) *
        ‖iteratedFDeriv Real (k - i) f v‖ := by
    gcongr with i _hi
    exact I₃ i
  _ = ∑ i in Finset.range (k + 1), (k.choose i * n.descFactorial i * ‖L‖ ^ n) *
        (‖v‖ ^ (n - i) * ‖iteratedFDeriv Real (k - i) f v‖) := by
    congr with i
    ring
  _ <= ∑ i in Finset.range (k + 1), (k.choose i * (n + 1 : Nat) ^ k * ‖L‖ ^ n) * C := by
    gcongr with i hi
    · norm_cast
      calc n.descFactorial i <= n ^ i := Nat.descFactorial_le_pow _ _
      _ <= (n + 1) ^ i := by gcongr; lia
      _ <= (n + 1) ^ k := by gcongr; exacts [le_add_self, Finset.mem_range_succ_iff.mp hi]
    · exact hv _ (by lia) _ (by lia)
  _ = (2 * n + 2) ^ k * (‖L‖ ^ n * C) := by
    simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, mul_one, ← mul_assoc,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ← mul_pow, mul_add]

中文:
引理 norm_iteratedFDeriv_fourierPowSMulRight
  证明: by
  /- We write `fourierPowSMulRight L f v n` as a composition of bilinear and multilinear maps,
  thanks to `fourierPowSMulRight_eq_comp`, and then we control the iterated derivatives of these
  thanks to general bounds on derivatives of bilinear and multilinear maps. More precisely,
  `fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v`. Here,
  `(- (2 * π * I))^n` contributes `(2π)^n` to the bound. The second product is bilinear, so the
  iterated derivative is controlled as a weighted sum of those of `v ↦ ∏ i, L v (m i)` and of `f`.

  The harder part is to control the iterated derivatives of `v ↦ ∏ i, L v (m i)`. For this, one
  argues that this is multilinear in `v`, to apply general bounds for iterated derivatives of
  multilinear maps. More precisely, we write it as the composition of a multilinear map `T` (making
  the product operation) and the tuple of linear maps `v ↦ (L v ⬝, ..., L v ⬝)` -/
  simp_rw [fourierPowSMulRight_eq_comp]
  -- first step: controlling the iterated derivatives of `v ↦ ∏ i, L v (m i)`, written below
  -- as `v ↦ T (fun _ ↦ L v)`, or `T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))`.
  let T : (W ->L[Real] Real) [×n]->L[Real] (W [×n]->L[Real] Real) :=
    compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n) Real)
  have I₁ m : ‖iteratedFDeriv Real m T (fun _ => L v)‖ <=
      n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m) := by
    have : ‖T‖ <= 1 := by
      apply (norm_compContinuousLinearMapLRight_le _ _).trans
      simp only [norm_mkPiAlgebra, le_refl]
    apply (ContinuousMultilinearMap.norm_iteratedFDeriv_le _ _ _).trans
    simp only [Fintype.card_fin]
    gcongr
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun _ => ?_)
    exact ContinuousLinearMap.le_opNorm _ _
  have I₂ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      (n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m)) * ‖L‖ ^ m := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (ContinuousMultilinearMap.contDiff _)
      _ (mod_cast le_top)]
    apply (norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    · exact I₁ m
    · exact ContinuousLinearMap.norm_pi_le_of_le (fun _ => le_rfl) (norm_nonneg _)
  have I₃ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      n.descFactorial m * ‖L‖ ^ n * ‖v‖ ^ (n - m) := by
    apply (I₂ m).trans (le_of_eq _)
    rcases le_or_gt m n with hm | hm
    · rw [show ‖L‖ ^ n = ‖L‖ ^ (m + (n - m)) by rw [Nat.add_sub_cancel' hm], pow_add]
      ring
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hm, CharP.cast_eq_zero, mul_one, zero_mul]
  -- second step: factor out the `(2 * π) ^ n` factor, and cancel it on both sides.
  have A : ContDiff Real K (fun y => T (fun _ => L y)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => L.contDiff)
  rw [iteratedFDeriv_const_smul_apply' (hf := ((smulRightL Real (fun _ => W)
    E).isBoundedBilinearMap.contDiff.comp₂ (A.of_le hk) (hf.of_le hk)).contDiffAt)]; rw [norm_smul (β := V [×k]->L[Real] (W [×n]->L[Real] E))]
  simp only [mul_assoc, norm_pow, norm_neg, Complex.norm_mul, Complex.norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_of_nonneg pi_nonneg, norm_I, mul_one, smulRightL_apply, ge_iff_le]
  gcongr
  -- third step: argue that the scalar multiplication is bilinear to bound the iterated derivatives
  -- of `v ↦ (∏ i, L v (m i)) • f v` in terms of those of `v ↦ (∏ i, L v (m i))` and of `f`.
  -- The former are controlled by the first step, the latter by the assumptions.
  apply (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ A hf _
    hk ContinuousMultilinearMap.norm_smulRightL_le).trans
  calc
  ∑ i in Finset.range (k + 1),
    k.choose i * ‖iteratedFDeriv Real i (fun (y : V) => T (fun _ => L y)) v‖ *
      ‖iteratedFDeriv Real (k - i) f v‖
    <= ∑ i in Finset.range (k + 1),
      k.choose i * (n.descFactorial i * ‖L‖ ^ n * ‖v‖ ^ (n - i)) *
        ‖iteratedFDeriv Real (k - i) f v‖ := by
    gcongr with i _hi
    exact I₃ i
  _ = ∑ i in Finset.range (k + 1), (k.choose i * n.descFactorial i * ‖L‖ ^ n) *
        (‖v‖ ^ (n - i) * ‖iteratedFDeriv Real (k - i) f v‖) := by
    congr with i
    ring
  _ <= ∑ i in Finset.range (k + 1), (k.choose i * (n + 1 : Nat) ^ k * ‖L‖ ^ n) * C := by
    gcongr with i hi
    · norm_cast
      calc n.descFactorial i <= n ^ i := Nat.descFactorial_le_pow _ _
      _ <= (n + 1) ^ i := by gcongr; lia
      _ <= (n + 1) ^ k := by gcongr; exacts [le_add_self, Finset.mem_range_succ_iff.mp hi]
    · exact hv _ (by lia) _ (by lia)
  _ = (2 * n + 2) ^ k * (‖L‖ ^ n * C) := by
    simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, mul_one, ← mul_assoc,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ← mul_pow, mul_add]
-/
lemma norm_iteratedFDeriv_fourierPowSMulRight
    {f : V -> E} {K : Nat∞ω} {C : Real} (hf : ContDiff Real K f) {n : Nat} {k : Nat} (hk : k <= K)
    {v : V} (hv : forall i <= k, forall j <= n, ‖v‖ ^ j * ‖iteratedFDeriv Real i f v‖ <= C) :
    ‖iteratedFDeriv Real k (fun v => fourierPowSMulRight L f v n) v‖ <=
      (2 * π) ^ n * (2 * n + 2) ^ k * ‖L‖ ^ n * C := by
  /- We write `fourierPowSMulRight L f v n` as a composition of bilinear and multilinear maps,
  thanks to `fourierPowSMulRight_eq_comp`, and then we control the iterated derivatives of these
  thanks to general bounds on derivatives of bilinear and multilinear maps. More precisely,
  `fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v`. Here,
  `(- (2 * π * I))^n` contributes `(2π)^n` to the bound. The second product is bilinear, so the
  iterated derivative is controlled as a weighted sum of those of `v ↦ ∏ i, L v (m i)` and of `f`.

  The harder part is to control the iterated derivatives of `v ↦ ∏ i, L v (m i)`. For this, one
  argues that this is multilinear in `v`, to apply general bounds for iterated derivatives of
  multilinear maps. More precisely, we write it as the composition of a multilinear map `T` (making
  the product operation) and the tuple of linear maps `v ↦ (L v ⬝, ..., L v ⬝)` -/
  simp_rw [fourierPowSMulRight_eq_comp]
  -- first step: controlling the iterated derivatives of `v ↦ ∏ i, L v (m i)`, written below
  -- as `v ↦ T (fun _ ↦ L v)`, or `T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))`.
  let T : (W ->L[Real] Real) [×n]->L[Real] (W [×n]->L[Real] Real) :=
    compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n) Real)
  have I₁ m : ‖iteratedFDeriv Real m T (fun _ => L v)‖ <=
      n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m) := by
    have : ‖T‖ <= 1 := by
      apply (norm_compContinuousLinearMapLRight_le _ _).trans
      simp only [norm_mkPiAlgebra, le_refl]
    apply (ContinuousMultilinearMap.norm_iteratedFDeriv_le _ _ _).trans
    simp only [Fintype.card_fin]
    gcongr
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun _ => ?_)
    exact ContinuousLinearMap.le_opNorm _ _
  have I₂ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      (n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m)) * ‖L‖ ^ m := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (ContinuousMultilinearMap.contDiff _)
      _ (mod_cast le_top)]
    apply (norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    · exact I₁ m
    · exact ContinuousLinearMap.norm_pi_le_of_le (fun _ => le_rfl) (norm_nonneg _)
  have I₃ m : ‖iteratedFDeriv Real m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) => L))) v‖ <=
      n.descFactorial m * ‖L‖ ^ n * ‖v‖ ^ (n - m) := by
    apply (I₂ m).trans (le_of_eq _)
    rcases le_or_gt m n with hm | hm
    · rw [show ‖L‖ ^ n = ‖L‖ ^ (m + (n - m)) by rw [Nat.add_sub_cancel' hm], pow_add]
      ring
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hm, CharP.cast_eq_zero, mul_one, zero_mul]
  -- second step: factor out the `(2 * π) ^ n` factor, and cancel it on both sides.
  have A : ContDiff Real K (fun y => T (fun _ => L y)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => L.contDiff)
  rw [iteratedFDeriv_const_smul_apply' (hf := ((smulRightL Real (fun _ => W)
    E).isBoundedBilinearMap.contDiff.comp₂ (A.of_le hk) (hf.of_le hk)).contDiffAt)]; rw [norm_smul (β := V [×k]->L[Real] (W [×n]->L[Real] E))]
  simp only [mul_assoc, norm_pow, norm_neg, Complex.norm_mul, Complex.norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_of_nonneg pi_nonneg, norm_I, mul_one, smulRightL_apply, ge_iff_le]
  gcongr
  -- third step: argue that the scalar multiplication is bilinear to bound the iterated derivatives
  -- of `v ↦ (∏ i, L v (m i)) • f v` in terms of those of `v ↦ (∏ i, L v (m i))` and of `f`.
  -- The former are controlled by the first step, the latter by the assumptions.
  apply (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ A hf _
    hk ContinuousMultilinearMap.norm_smulRightL_le).trans
  calc
  ∑ i in Finset.range (k + 1),
    k.choose i * ‖iteratedFDeriv Real i (fun (y : V) => T (fun _ => L y)) v‖ *
      ‖iteratedFDeriv Real (k - i) f v‖
    <= ∑ i in Finset.range (k + 1),
      k.choose i * (n.descFactorial i * ‖L‖ ^ n * ‖v‖ ^ (n - i)) *
        ‖iteratedFDeriv Real (k - i) f v‖ := by
    gcongr with i _hi
    exact I₃ i
  _ = ∑ i in Finset.range (k + 1), (k.choose i * n.descFactorial i * ‖L‖ ^ n) *
        (‖v‖ ^ (n - i) * ‖iteratedFDeriv Real (k - i) f v‖) := by
    congr with i
    ring
  _ <= ∑ i in Finset.range (k + 1), (k.choose i * (n + 1 : Nat) ^ k * ‖L‖ ^ n) * C := by
    gcongr with i hi
    · norm_cast
      calc n.descFactorial i <= n ^ i := Nat.descFactorial_le_pow _ _
      _ <= (n + 1) ^ i := by gcongr; lia
      _ <= (n + 1) ^ k := by gcongr; exacts [le_add_self, Finset.mem_range_succ_iff.mp hi]
    · exact hv _ (by lia) _ (by lia)
  _ = (2 * n + 2) ^ k * (‖L‖ ^ n * C) := by
    simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, mul_one, ← mul_assoc,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ← mul_pow, mul_add]

variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V}

section SecondCountableTopology

variable [SecondCountableTopology V]

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight
  proof: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

中文:
引理 _root_.测度论.AEStronglyMeasurable.fourierPowSMulRight
  证明: by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.fun_const_smul, Continuous, Continuous.aestronglyMeasurable, Continuous.comp, L.continuous, aestronglyMeasurable, continuous, continuous_pi, fourierPowSMulRight_eq_comp, fun_const_smul, map_continuous, simp_rw, smulRightL
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight
    (hf : AEStronglyMeasurable f μ) (n : Nat) :
    AEStronglyMeasurable (fun v => fourierPowSMulRight L f v n) μ := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.fun_const_smul
  apply (smulRightL Real (fun (_ : Fin n) => W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ => L.continuous))

/--
lemma `integrable_fourierPowSMulRight` / 引理 `integrable_fourierPowSMulRight`

English:
lemma integrable_fourierPowSMulRight
  statement: {n : Nat} (hf : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ)
  proof: by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' (h'f.fourierPowSMulRight L n) ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))

中文:
引理 integrable_fourierPowSMulRight
  结论: {n : 自然数} (hf : 可积 (fun v => ‖v‖ ^ n * ‖f v‖) μ)
  证明: by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' (h'f.fourierPowSMulRight L n) ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))

Depends on / 依赖: const_mul, f.fourierPowSMulRight, filter_upwards, fourierPowSMulRight, hf.const_mul, le_of_eq, norm_fourierPowSMulRight_le
-/
lemma integrable_fourierPowSMulRight {n : Nat} (hf : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) : Integrable (fun v => fourierPowSMulRight L f v n) μ := by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' (h'f.fourierPowSMulRight L n) ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))

/--
lemma `hasFTaylorSeriesUpTo_fourierIntegral` / 引理 `hasFTaylorSeriesUpTo_fourierIntegral`

English:
lemma hasFTaylorSeriesUpTo_fourierIntegral
  statement: {N : Nat∞ω}
  proof: by
  constructor
  · intro w
    rw [curry0_apply]; rw [Matrix.zero_empty]; rw [fourierIntegral_continuousMultilinearMap_apply'
      (integrable_fourierPowSMulRight L (hf 0 bot_le) h'f)]
    simp only [fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_smul]
  · intro n hn w
    have I₁ : Integrable (fun v => fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight L (hf n hn.le) h'f
    have I₂ : Integrable (fun v => ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)).const_mul
          ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul (h'f.fourierPowSMulRight L n).norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        <= ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v => fourierPowSMulRight L f v (n + 1)) μ :=
      integrable_fourierPowSMulRight L (hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)) h'f
    have I₄ : Integrable
        (fun v => fourierSMulRight L (fun v => fourierPowSMulRight L f v n) v) μ := by
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' (h'f.fourierPowSMulRight L n).fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v (n + 1)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₁₂
          (fourierSMulRight L fun v => fourierPowSMulRight L f v n) w := by
      ext w' m
      rw [curryLeft_apply]; rw [fourierIntegral_continuousMultilinearMap_apply' I₃]; rw [fourierIntegral_continuousLinearMap_apply' I₄]; rw [fourierIntegral_continuousMultilinearMap_apply' (I₄.apply_continuousLinearMap _)]
      congr with v
      simp only [fourierPowSMulRight_apply, mul_comm, pow_succ, neg_mul, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_smul, fourierSMulRight_apply,
        neg_apply, smul_apply, smul_comm (M := Real) (N := Complex) (α := E), smul_smul]
    exact E ▸ hasFDerivAt_fourierIntegral L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight L (hf n hn) h'f

中文:
引理 hasFTaylorSeriesUpTo_fourier整数egral
  结论: {N : 自然数∞ω}
  证明: by
  constructor
  · intro w
    rw [curry0_apply]; rw [Matrix.zero_empty]; rw [fourierIntegral_continuousMultilinearMap_apply'
      (integrable_fourierPowSMulRight L (hf 0 bot_le) h'f)]
    simp only [fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_smul]
  · intro n hn w
    have I₁ : Integrable (fun v => fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight L (hf n hn.le) h'f
    have I₂ : Integrable (fun v => ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)).const_mul
          ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul (h'f.fourierPowSMulRight L n).norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        <= ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v => fourierPowSMulRight L f v (n + 1)) μ :=
      integrable_fourierPowSMulRight L (hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)) h'f
    have I₄ : Integrable
        (fun v => fourierSMulRight L (fun v => fourierPowSMulRight L f v n) v) μ := by
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' (h'f.fourierPowSMulRight L n).fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v (n + 1)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₁₂
          (fourierSMulRight L fun v => fourierPowSMulRight L f v n) w := by
      ext w' m
      rw [curryLeft_apply]; rw [fourierIntegral_continuousMultilinearMap_apply' I₃]; rw [fourierIntegral_continuousLinearMap_apply' I₄]; rw [fourierIntegral_continuousMultilinearMap_apply' (I₄.apply_continuousLinearMap _)]
      congr with v
      simp only [fourierPowSMulRight_apply, mul_comm, pow_succ, neg_mul, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_smul, fourierSMulRight_apply,
        neg_apply, smul_apply, smul_comm (M := Real) (N := Complex) (α := E), smul_smul]
    exact E ▸ hasFDerivAt_fourierIntegral L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight L (hf n hn) h'f

Depends on / 依赖: Finset, Finset.prod_empty, Finset.univ_eq_empty, Integrable, Matrix, Matrix.zero_empty, bot_le, curry0_apply, fourierIntegral_continuousMultilinearMap_apply, fourierPowSMulRight, fourierPowSMulRight_apply, hn.le, integrable_fourierPowSMulRight, one_smul, pow_zero, prod_empty, univ_eq_empty, zero_empty
-/
lemma hasFTaylorSeriesUpTo_fourierIntegral {N : Nat∞ω}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fun w n => fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n) w) := by
  constructor
  · intro w
    rw [curry0_apply]; rw [Matrix.zero_empty]; rw [fourierIntegral_continuousMultilinearMap_apply'
      (integrable_fourierPowSMulRight L (hf 0 bot_le) h'f)]
    simp only [fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_smul]
  · intro n hn w
    have I₁ : Integrable (fun v => fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight L (hf n hn.le) h'f
    have I₂ : Integrable (fun v => ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)).const_mul
          ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul (h'f.fourierPowSMulRight L n).norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        <= ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v => fourierPowSMulRight L f v (n + 1)) μ :=
      integrable_fourierPowSMulRight L (hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)) h'f
    have I₄ : Integrable
        (fun v => fourierSMulRight L (fun v => fourierPowSMulRight L f v n) v) μ := by
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' (h'f.fourierPowSMulRight L n).fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v (n + 1)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₁₂
          (fourierSMulRight L fun v => fourierPowSMulRight L f v n) w := by
      ext w' m
      rw [curryLeft_apply]; rw [fourierIntegral_continuousMultilinearMap_apply' I₃]; rw [fourierIntegral_continuousLinearMap_apply' I₄]; rw [fourierIntegral_continuousMultilinearMap_apply' (I₄.apply_continuousLinearMap _)]
      congr with v
      simp only [fourierPowSMulRight_apply, mul_comm, pow_succ, neg_mul, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_smul, fourierSMulRight_apply,
        neg_apply, smul_apply, smul_comm (M := Real) (N := Complex) (α := E), smul_smul]
    exact E ▸ hasFDerivAt_fourierIntegral L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight L (hf n hn) h'f

/--
lemma `hasFTaylorSeriesUpTo_fourierIntegral'` / 引理 `hasFTaylorSeriesUpTo_fourierIntegral'`

English:
lemma hasFTaylorSeriesUpTo_fourierIntegral'
  statement: {N : Nat∞}
  proof: hasFTaylorSeriesUpTo_fourierIntegral _ (fun n hn => hf n (mod_cast hn)) h'f

中文:
引理 hasFTaylorSeriesUpTo_fourier整数egral'
  结论: {N : 自然数∞}
  证明: hasFTaylorSeriesUpTo_fourierIntegral _ (fun n hn => hf n (mod_cast hn)) h'f

Depends on / 依赖: hasFTaylorSeriesUpTo_fourierIntegral, mod_cast
-/
lemma hasFTaylorSeriesUpTo_fourierIntegral' {N : Nat∞}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fun w n => fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n) w) :=
  hasFTaylorSeriesUpTo_fourierIntegral _ (fun n hn => hf n (mod_cast hn)) h'f

/--
theorem `contDiff_fourierIntegral` / 定理 `contDiff_fourierIntegral`

English:
theorem contDiff_fourierIntegral
  statement: {N : Nat∞}
  proof: by
  by_cases h'f : Integrable f μ
  · exact (hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f.1).contDiff
  · have : fourierIntegral 𝐞 μ L.toLinearMap₁₂ f = 0 := by
      ext w; simp [fourierIntegral, integral, h'f]
    simpa [this] using! contDiff_const

中文:
定理 contDiff_fourier整数egral
  结论: {N : 自然数∞}
  证明: by
  by_cases h'f : Integrable f μ
  · exact (hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f.1).contDiff
  · have : fourierIntegral 𝐞 μ L.toLinearMap₁₂ f = 0 := by
      ext w; simp [fourierIntegral, integral, h'f]
    simpa [this] using! contDiff_const

Depends on / 依赖: Integrable, L.toLinearMap, contDiff, contDiff_const, fourierIntegral, hasFTaylorSeriesUpTo_fourierIntegral, integral
-/
theorem contDiff_fourierIntegral {N : Nat∞}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) :
    ContDiff Real N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  by_cases h'f : Integrable f μ
  · exact (hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f.1).contDiff
  · have : fourierIntegral 𝐞 μ L.toLinearMap₁₂ f = 0 := by
      ext w; simp [fourierIntegral, integral, h'f]
    simpa [this] using! contDiff_const

/--
lemma `iteratedFDeriv_fourierIntegral` / 引理 `iteratedFDeriv_fourierIntegral`

English:
lemma iteratedFDeriv_fourierIntegral
  statement: {N : Nat∞}
  proof: by
  ext w : 1
  exact ((hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f).eq_iteratedFDeriv
    (mod_cast hn) w).symm

中文:
引理 iteratedFDeriv_fourier整数egral
  结论: {N : 自然数∞}
  证明: by
  ext w : 1
  exact ((hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f).eq_iteratedFDeriv
    (mod_cast hn) w).symm

Depends on / 依赖: eq_iteratedFDeriv, hasFTaylorSeriesUpTo_fourierIntegral, mod_cast
-/
lemma iteratedFDeriv_fourierIntegral {N : Nat∞}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) {n : Nat} (hn : n <= N) :
    iteratedFDeriv Real n (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n) := by
  ext w : 1
  exact ((hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f).eq_iteratedFDeriv
    (mod_cast hn) w).symm

end SecondCountableTopology

/--
theorem `fourierIntegral_iteratedFDeriv` / 定理 `fourierIntegral_iteratedFDeriv`

English:
theorem fourierIntegral_iteratedFDeriv
  statement: [FiniteDimensional Real V]
  proof: by
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty,
      neg_apply, ContinuousLinearMap.flip_apply, Finset.prod_empty, one_smul,
      fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 bot_le))]
  | succ n ih =>
    ext w m
    have J : Integrable (fderiv Real (iteratedFDeriv Real n f)) μ := by
      specialize h'f (n + 1) hn
      rwa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
          LinearIsometryEquiv.integrable_comp_iff (𝕜 := Real) (φ := fderiv Real (iteratedFDeriv Real n f))]
        at h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv Real (iteratedFDeriv Real n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ hn)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, neg_apply,
        ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _))]; rw [← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    have h'n : n < N := (Nat.cast_lt.mpr n.lt_succ_self).trans_le hn
    rw [fourierIntegral_fderiv _ (h'f n h'n.le)
      (hf.differentiable_iteratedFDeriv (mod_cast h'n)) J]
    simp only [ih h'n.le, fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply,
      neg_smul, smul_neg, neg_neg, smul_apply, fourierPowSMulRight_apply, ← coe_smul (E := E),
      smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring

中文:
定理 fourier整数egral_iteratedFDeriv
  结论: [有限维 实数 V]
  证明: by
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty,
      neg_apply, ContinuousLinearMap.flip_apply, Finset.prod_empty, one_smul,
      fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 bot_le))]
  | succ n ih =>
    ext w m
    have J : Integrable (fderiv Real (iteratedFDeriv Real n f)) μ := by
      specialize h'f (n + 1) hn
      rwa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
          LinearIsometryEquiv.integrable_comp_iff (𝕜 := Real) (φ := fderiv Real (iteratedFDeriv Real n f))]
        at h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv Real (iteratedFDeriv Real n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ hn)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, neg_apply,
        ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _))]; rw [← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    have h'n : n < N := (Nat.cast_lt.mpr n.lt_succ_self).trans_le hn
    rw [fourierIntegral_fderiv _ (h'f n h'n.le)
      (hf.differentiable_iteratedFDeriv (mod_cast h'n)) J]
    simp only [ih h'n.le, fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply,
      neg_smul, smul_neg, neg_neg, smul_apply, fourierPowSMulRight_apply, ← coe_smul (E := E),
      smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip_apply, Finset, Finset.prod_empty, Finset.univ_eq_empty, Function, Function.comp_def, Integrable, LinearIsometryEquiv, LinearIsometryEquiv.integrable_comp_iff, bot_le, comp_def, fderiv, flip_apply, fourierIntegral_continuousMultilinearMap_apply, fourierPowSMulRight_apply, integrable_comp_iff, iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_zero_apply
-/
theorem fourierIntegral_iteratedFDeriv [FiniteDimensional Real V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f) μ) {n : Nat} (hn : n <= N) :
    fourierIntegral 𝐞 μ L.toLinearMap₁₂ (iteratedFDeriv Real n f)
      = (fun w => fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w n) := by
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty,
      neg_apply, ContinuousLinearMap.flip_apply, Finset.prod_empty, one_smul,
      fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 bot_le))]
  | succ n ih =>
    ext w m
    have J : Integrable (fderiv Real (iteratedFDeriv Real n f)) μ := by
      specialize h'f (n + 1) hn
      rwa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
          LinearIsometryEquiv.integrable_comp_iff (𝕜 := Real) (φ := fderiv Real (iteratedFDeriv Real n f))]
        at h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv Real (iteratedFDeriv Real n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ hn)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, neg_apply,
        ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _))]; rw [← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    have h'n : n < N := (Nat.cast_lt.mpr n.lt_succ_self).trans_le hn
    rw [fourierIntegral_fderiv _ (h'f n h'n.le)
      (hf.differentiable_iteratedFDeriv (mod_cast h'n)) J]
    simp only [ih h'n.le, fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply,
      neg_smul, smul_neg, neg_neg, smul_apply, fourierPowSMulRight_apply, ← coe_smul (E := E),
      smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring

/--
theorem `fourierPowSMulRight_iteratedFDeriv_fourierIntegral` / 定理 `fourierPowSMulRight_iteratedFDeriv_fourierIntegral`

English:
theorem fourierPowSMulRight_iteratedFDeriv_fourierIntegral
  statement: [FiniteDimensional Real V]
  proof: by
  rw [fourierIntegral_iteratedFDeriv (N := N) _ (hf.fourierPowSMulRight _ _) _ hn]
  · congr
    rw [iteratedFDeriv_fourierIntegral (N := K) _ _ hf.continuous.aestronglyMeasurable hk]
    intro k hk
    simpa only [norm_iteratedFDeriv_zero] using h'f k 0 hk bot_le
  · intro m hm
    have I : Integrable (fun v => ∑ p in Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
      apply integrable_finsetSum _ (fun p hp => ?_)
      simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
      exact h'f _ _ ((Nat.cast_le.2 hp.1).trans hk) ((Nat.cast_le.2 hp.2).trans hm)
    apply (I.const_mul ((2 * π) ^ k * (2 * k + 2) ^ m * ‖L‖ ^ k)).mono'
      ((hf.fourierPowSMulRight L k).continuous_iteratedFDeriv (mod_cast hm)).aestronglyMeasurable
    filter_upwards with v
    refine norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hm) (fun i hi j hj => ?_)
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simpa only [Finset.mem_product, Finset.mem_range_succ_iff] using ⟨hj, hi⟩

中文:
定理 fourierPowSMulRight_iteratedFDeriv_fourier整数egral
  结论: [有限维 实数 V]
  证明: by
  rw [fourierIntegral_iteratedFDeriv (N := N) _ (hf.fourierPowSMulRight _ _) _ hn]
  · congr
    rw [iteratedFDeriv_fourierIntegral (N := K) _ _ hf.continuous.aestronglyMeasurable hk]
    intro k hk
    simpa only [norm_iteratedFDeriv_zero] using h'f k 0 hk bot_le
  · intro m hm
    have I : Integrable (fun v => ∑ p in Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
      apply integrable_finsetSum _ (fun p hp => ?_)
      simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
      exact h'f _ _ ((Nat.cast_le.2 hp.1).trans hk) ((Nat.cast_le.2 hp.2).trans hm)
    apply (I.const_mul ((2 * π) ^ k * (2 * k + 2) ^ m * ‖L‖ ^ k)).mono'
      ((hf.fourierPowSMulRight L k).continuous_iteratedFDeriv (mod_cast hm)).aestronglyMeasurable
    filter_upwards with v
    refine norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hm) (fun i hi j hj => ?_)
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simpa only [Finset.mem_product, Finset.mem_range_succ_iff] using ⟨hj, hi⟩

Depends on / 依赖: Finset, Finset.mem_product, Finset.mem_range_succ_if, Finset.range, Integrable, aestronglyMeasurable, bot_le, continuous, fourierIntegral_iteratedFDeriv, fourierPowSMulRight, hf.continuous.aestronglyMeasurable, hf.fourierPowSMulRight, integrable_finsetSum, iteratedFDeriv, iteratedFDeriv_fourierIntegral, mem_product, mem_range_succ_if, norm_iteratedFDeriv_zero
-/
theorem fourierPowSMulRight_iteratedFDeriv_fourierIntegral [FiniteDimensional Real V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ)
    {k n : Nat} (hk : k <= K) (hn : n <= N) {w : W} :
    fourierPowSMulRight (-L.flip)
      (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n =
    fourierIntegral 𝐞 μ L.toLinearMap₁₂
      (iteratedFDeriv Real n (fun v => fourierPowSMulRight L f v k)) w := by
  rw [fourierIntegral_iteratedFDeriv (N := N) _ (hf.fourierPowSMulRight _ _) _ hn]
  · congr
    rw [iteratedFDeriv_fourierIntegral (N := K) _ _ hf.continuous.aestronglyMeasurable hk]
    intro k hk
    simpa only [norm_iteratedFDeriv_zero] using h'f k 0 hk bot_le
  · intro m hm
    have I : Integrable (fun v => ∑ p in Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
      apply integrable_finsetSum _ (fun p hp => ?_)
      simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
      exact h'f _ _ ((Nat.cast_le.2 hp.1).trans hk) ((Nat.cast_le.2 hp.2).trans hm)
    apply (I.const_mul ((2 * π) ^ k * (2 * k + 2) ^ m * ‖L‖ ^ k)).mono'
      ((hf.fourierPowSMulRight L k).continuous_iteratedFDeriv (mod_cast hm)).aestronglyMeasurable
    filter_upwards with v
    refine norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hm) (fun i hi j hj => ?_)
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simpa only [Finset.mem_product, Finset.mem_range_succ_iff] using ⟨hj, hi⟩

/--
theorem `norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le` / 定理 `norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le`

English:
theorem norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le
  statement: [FiniteDimensional Real V]
  proof: by
  rw [fourierPowSMulRight_iteratedFDeriv_fourierIntegral L hf h'f hk hn]
  apply (norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  have I p (hp : p in Finset.range (k + 1) ×ˢ Finset.range (n + 1)) :
      Integrable (fun v => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
    simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
    exact h'f _ _ (le_trans (by simpa using hp.1) hk) (le_trans (by simpa using hp.2) hn)
  rw [← integral_finsetSum _ I]; rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards with v using norm_nonneg _
  · exact (integrable_finsetSum _ I).const_mul _
  · filter_upwards with v
    apply norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hn) _
    intro i hi j hj
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simp only [Finset.mem_product, Finset.mem_range_succ_iff]
      exact ⟨hj, hi⟩

中文:
定理 norm_fourierPowSMulRight_iteratedFDeriv_fourier整数egral_le
  结论: [有限维 实数 V]
  证明: by
  rw [fourierPowSMulRight_iteratedFDeriv_fourierIntegral L hf h'f hk hn]
  apply (norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  have I p (hp : p in Finset.range (k + 1) ×ˢ Finset.range (n + 1)) :
      Integrable (fun v => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
    simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
    exact h'f _ _ (le_trans (by simpa using hp.1) hk) (le_trans (by simpa using hp.2) hn)
  rw [← integral_finsetSum _ I]; rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards with v using norm_nonneg _
  · exact (integrable_finsetSum _ I).const_mul _
  · filter_upwards with v
    apply norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hn) _
    intro i hi j hj
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simp only [Finset.mem_product, Finset.mem_range_succ_iff]
      exact ⟨hj, hi⟩

Depends on / 依赖: Finset, Finset.mem_product, Finset.mem_range_succ_iff, Finset.range, Integrable, fourierPowSMulRight_iteratedFDeriv_fourierIntegral, integral_const_mul, integral_finsetSum, integral_mo, iteratedFDeriv, le_trans, mem_product, mem_range_succ_iff, norm_fourierIntegral_le_integral_norm
-/
theorem norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le [FiniteDimensional Real V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ)
    {k n : Nat} (hk : k <= K) (hn : n <= N) {w : W} :
    ‖fourierPowSMulRight (-L.flip)
      (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ <=
    (2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k * ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ := by
  rw [fourierPowSMulRight_iteratedFDeriv_fourierIntegral L hf h'f hk hn]
  apply (norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  have I p (hp : p in Finset.range (k + 1) ×ˢ Finset.range (n + 1)) :
      Integrable (fun v => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) μ := by
    simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
    exact h'f _ _ (le_trans (by simpa using hp.1) hk) (le_trans (by simpa using hp.2) hn)
  rw [← integral_finsetSum _ I]; rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards with v using norm_nonneg _
  · exact (integrable_finsetSum _ I).const_mul _
  · filter_upwards with v
    apply norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hn) _
    intro i hi j hj
    apply Finset.single_le_sum (f := fun p => ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simp only [Finset.mem_product, Finset.mem_range_succ_iff]
      exact ⟨hj, hi⟩

/--
lemma `pow_mul_norm_iteratedFDeriv_fourierIntegral_le` / 引理 `pow_mul_norm_iteratedFDeriv_fourierIntegral_le`

English:
lemma pow_mul_norm_iteratedFDeriv_fourierIntegral_le
  statement: [FiniteDimensional Real V]
  proof: calc
  |L v w| ^ n * ‖(iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖
  _ <= (2 * π) ^ n
      * (|L v w| ^ n * ‖iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w‖) := by
    apply le_mul_of_one_le_left (by positivity)
    apply one_le_pow₀
    linarith [one_le_pi_div_two]
  _ = ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n (fun _ => v)‖ := by
    simp [norm_smul, abs_of_nonneg pi_nonneg]
  _ <= ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ * ∏ _ : Fin n, ‖v‖ :=
    le_opNorm _ _
  _ <= ((2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ) * ‖v‖ ^ n := by
    gcongr
    · apply norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le _ hf h'f hk hn
    · simp
  _ = ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ := by
    simp [mul_pow]
    ring

中文:
引理 pow_mul_norm_iteratedFDeriv_fourier整数egral_le
  结论: [有限维 实数 V]
  证明: calc
  |L v w| ^ n * ‖(iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖
  _ <= (2 * π) ^ n
      * (|L v w| ^ n * ‖iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w‖) := by
    apply le_mul_of_one_le_left (by positivity)
    apply one_le_pow₀
    linarith [one_le_pi_div_two]
  _ = ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n (fun _ => v)‖ := by
    simp [norm_smul, abs_of_nonneg pi_nonneg]
  _ <= ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ * ∏ _ : Fin n, ‖v‖ :=
    le_opNorm _ _
  _ <= ((2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ) * ‖v‖ ^ n := by
    gcongr
    · apply norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le _ hf h'f hk hn
    · simp
  _ = ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ := by
    simp [mul_pow]
    ring
-/
lemma pow_mul_norm_iteratedFDeriv_fourierIntegral_le [FiniteDimensional Real V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ)
    {k n : Nat} (hk : k <= K) (hn : n <= N) (v : V) (w : W) :
    |L v w| ^ n * ‖(iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖ <=
      ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ := calc
  |L v w| ^ n * ‖(iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖
  _ <= (2 * π) ^ n
      * (|L v w| ^ n * ‖iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w‖) := by
    apply le_mul_of_one_le_left (by positivity)
    apply one_le_pow₀
    linarith [one_le_pi_div_two]
  _ = ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n (fun _ => v)‖ := by
    simp [norm_smul, abs_of_nonneg pi_nonneg]
  _ <= ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ * ∏ _ : Fin n, ‖v‖ :=
    le_opNorm _ _
  _ <= ((2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ) * ‖v‖ ^ n := by
    gcongr
    · apply norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le _ hf h'f hk hn
    · simp
  _ = ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂μ := by
    simp [mul_pow]
    ring

end VectorFourier

namespace Real
open VectorFourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] {f : V -> E}

/--
theorem `hasFDerivAt_fourier` / 定理 `hasFDerivAt_fourier`

English:
theorem hasFDerivAt_fourier
  proof: VectorFourier.hasFDerivAt_fourierIntegral (innerSL Real) hf_int hvf_int x

中文:
定理 hasFDerivAt_fourier
  证明: VectorFourier.hasFDerivAt_fourierIntegral (innerSL Real) hf_int hvf_int x

Depends on / 依赖: VectorFourier, VectorFourier.hasFDerivAt_fourierIntegral, hasFDerivAt_fourierIntegral, hf_int, hvf_int, innerSL
-/
theorem hasFDerivAt_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)) (x : V) :
    HasFDerivAt (𝓕 f) (𝓕 (fourierSMulRight (innerSL Real) f) x) x :=
  VectorFourier.hasFDerivAt_fourierIntegral (innerSL Real) hf_int hvf_int x

/--
theorem `fderiv_fourier` / 定理 `fderiv_fourier`

English:
theorem fderiv_fourier
  proof: VectorFourier.fderiv_fourierIntegral (innerSL Real) hf_int hvf_int

中文:
定理 fderiv_fourier
  证明: VectorFourier.fderiv_fourierIntegral (innerSL Real) hf_int hvf_int

Depends on / 依赖: VectorFourier, VectorFourier.fderiv_fourierIntegral, fderiv_fourierIntegral, hf_int, hvf_int, innerSL
-/
theorem fderiv_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)) :
    fderiv Real (𝓕 f) = 𝓕 (fourierSMulRight (innerSL Real) f) :=
  VectorFourier.fderiv_fourierIntegral (innerSL Real) hf_int hvf_int

/--
theorem `differentiable_fourier` / 定理 `differentiable_fourier`

English:
theorem differentiable_fourier
  proof: VectorFourier.differentiable_fourierIntegral (innerSL Real) hf_int hvf_int

中文:
定理 differentiable_fourier
  证明: VectorFourier.differentiable_fourierIntegral (innerSL Real) hf_int hvf_int

Depends on / 依赖: VectorFourier, VectorFourier.differentiable_fourierIntegral, differentiable_fourierIntegral, hf_int, hvf_int, innerSL
-/
theorem differentiable_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)) :
    Differentiable Real (𝓕 f) :=
  VectorFourier.differentiable_fourierIntegral (innerSL Real) hf_int hvf_int

/--
theorem `fourier_fderiv` / 定理 `fourier_fderiv`

English:
theorem fourier_fderiv
  proof: by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL Real) hf h'f hf'

中文:
定理 fourier_fderiv
  证明: by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL Real) hf h'f hf'

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_fderiv, flip_innerSL_real, fourierIntegral_fderiv, innerSL
-/
theorem fourier_fderiv
    (hf : Integrable f) (h'f : Differentiable Real f) (hf' : Integrable (fderiv Real f)) :
    𝓕 (fderiv Real f) = fourierSMulRight (-innerSL Real) (𝓕 f) := by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL Real) hf h'f hf'

/--
theorem `contDiff_fourier` / 定理 `contDiff_fourier`

English:
theorem contDiff_fourier
  statement: {N : Nat∞}
  proof: VectorFourier.contDiff_fourierIntegral (innerSL Real) hf

中文:
定理 contDiff_fourier
  结论: {N : 自然数∞}
  证明: VectorFourier.contDiff_fourierIntegral (innerSL Real) hf

Depends on / 依赖: VectorFourier, VectorFourier.contDiff_fourierIntegral, contDiff_fourierIntegral, innerSL
-/
theorem contDiff_fourier {N : Nat∞}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖)) :
    ContDiff Real N (𝓕 f) :=
  VectorFourier.contDiff_fourierIntegral (innerSL Real) hf

/--
theorem `iteratedFDeriv_fourier` / 定理 `iteratedFDeriv_fourier`

English:
theorem iteratedFDeriv_fourier
  statement: {N : Nat∞}
  proof: VectorFourier.iteratedFDeriv_fourierIntegral (innerSL Real) hf h'f hn

中文:
定理 iteratedFDeriv_fourier
  结论: {N : 自然数∞}
  证明: VectorFourier.iteratedFDeriv_fourierIntegral (innerSL Real) hf h'f hn

Depends on / 依赖: VectorFourier, VectorFourier.iteratedFDeriv_fourierIntegral, f.hom, innerSL, iteratedFDeriv_fourierIntegral
-/
theorem iteratedFDeriv_fourier {N : Nat∞}
    (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖))
    (h'f : AEStronglyMeasurable f) {n : Nat} (hn : n <= N) :
    iteratedFDeriv Real n (𝓕 f) = 𝓕 (fun v => fourierPowSMulRight (innerSL Real) f v n) :=
  VectorFourier.iteratedFDeriv_fourierIntegral (innerSL Real) hf h'f hn

/--
theorem `fourier_iteratedFDeriv` / 定理 `fourier_iteratedFDeriv`

English:
theorem fourier_iteratedFDeriv
  statement: {N : Nat∞} (hf : ContDiff Real N f)
  proof: by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL Real) hf h'f hn

中文:
定理 fourier_iteratedFDeriv
  结论: {N : 自然数∞} (hf : 连续可微 实数 N f)
  证明: by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL Real) hf h'f hn

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_iteratedFDeriv, f.hom, flip_innerSL_real, fourierIntegral_iteratedFDeriv, innerSL, nnnorm
-/
theorem fourier_iteratedFDeriv {N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f)) {n : Nat} (hn : n <= N) :
    𝓕 (iteratedFDeriv Real n f)
      = (fun w => fourierPowSMulRight (-innerSL Real) (𝓕 f) w n) := by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL Real) hf h'f hn

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- simp followed by positivity
/--
lemma `pow_mul_norm_iteratedFDeriv_fourier_le` / 引理 `pow_mul_norm_iteratedFDeriv_fourier_le`

English:
lemma pow_mul_norm_iteratedFDeriv_fourier_le
  proof: by
  have Z : ‖w‖ ^ n * (‖w‖ ^ n * ‖iteratedFDeriv Real k (𝓕 f) w‖) <=
      ‖w‖ ^ n * ((2 * (π * ‖innerSL (E := V) Real‖)) ^ k * ((2 * k + 2) ^ n *
          ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
            ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂volume)) := by
    have := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (innerSL Real) hf h'f hk hn
      w w
    simp only [innerSL_apply_apply _ w w, real_inner_self_eq_norm_sq w, abs_pow, abs_norm,
      mul_assoc] at this
    rwa [pow_two, mul_pow, mul_assoc] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, one_mul, mul_one, zero_add, Finset.range_one, Finset.product_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk, norm_iteratedFDeriv_zero] at Z ⊢
    apply Z.trans
    conv_rhs => rw [← mul_one π]
    gcongr
    exact norm_innerSL_le _
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hn]
    positivity
  rw [mul_le_mul_iff_right₀ (pow_pos (by simp [hw]) n)] at Z
  apply Z.trans
  conv_rhs => rw [← mul_one π]
  simp only [mul_assoc]
  gcongr
  exact norm_innerSL_le _

中文:
引理 pow_mul_norm_iteratedFDeriv_fourier_le
  证明: by
  have Z : ‖w‖ ^ n * (‖w‖ ^ n * ‖iteratedFDeriv Real k (𝓕 f) w‖) <=
      ‖w‖ ^ n * ((2 * (π * ‖innerSL (E := V) Real‖)) ^ k * ((2 * k + 2) ^ n *
          ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
            ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂volume)) := by
    have := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (innerSL Real) hf h'f hk hn
      w w
    simp only [innerSL_apply_apply _ w w, real_inner_self_eq_norm_sq w, abs_pow, abs_norm,
      mul_assoc] at this
    rwa [pow_two, mul_pow, mul_assoc] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, one_mul, mul_one, zero_add, Finset.range_one, Finset.product_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk, norm_iteratedFDeriv_zero] at Z ⊢
    apply Z.trans
    conv_rhs => rw [← mul_one π]
    gcongr
    exact norm_innerSL_le _
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hn]
    positivity
  rw [mul_le_mul_iff_right₀ (pow_pos (by simp [hw]) n)] at Z
  apply Z.trans
  conv_rhs => rw [← mul_one π]
  simp only [mul_assoc]
  gcongr
  exact norm_innerSL_le _

Depends on / 依赖: Finset, Finset.range, VectorFourier, VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le, abs_norm, abs_pow, innerSL, innerSL_apply_apply, iteratedFDeriv, mul_ass, mul_assoc, mul_pow, pow_mul_norm_iteratedFDeriv_fourierIntegral_le, pow_two, real_inner_self_eq_norm_sq, volume
-/
lemma pow_mul_norm_iteratedFDeriv_fourier_le
    {K N : Nat∞} (hf : ContDiff Real N f)
    (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖))
    {k n : Nat} (hk : k <= K) (hn : n <= N) (w : V) :
    ‖w‖ ^ n * ‖iteratedFDeriv Real k (𝓕 f) w‖ <= (2 * π) ^ k * (2 * k + 2) ^ n *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ := by
  have Z : ‖w‖ ^ n * (‖w‖ ^ n * ‖iteratedFDeriv Real k (𝓕 f) w‖) <=
      ‖w‖ ^ n * ((2 * (π * ‖innerSL (E := V) Real‖)) ^ k * ((2 * k + 2) ^ n *
          ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
            ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv Real p.2 f v‖ ∂volume)) := by
    have := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (innerSL Real) hf h'f hk hn
      w w
    simp only [innerSL_apply_apply _ w w, real_inner_self_eq_norm_sq w, abs_pow, abs_norm,
      mul_assoc] at this
    rwa [pow_two, mul_pow, mul_assoc] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, one_mul, mul_one, zero_add, Finset.range_one, Finset.product_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk, norm_iteratedFDeriv_zero] at Z ⊢
    apply Z.trans
    conv_rhs => rw [← mul_one π]
    gcongr
    exact norm_innerSL_le _
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hn]
    positivity
  rw [mul_le_mul_iff_right₀ (pow_pos (by simp [hw]) n)] at Z
  apply Z.trans
  conv_rhs => rw [← mul_one π]
  simp only [mul_assoc]
  gcongr
  exact norm_innerSL_le _

/--
lemma `hasDerivAt_fourier` / 引理 `hasDerivAt_fourier`

English:
lemma hasDerivAt_fourier
  proof: by
  have hf'' : Integrable (fun v : Real => ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using! hf'.norm
.flip let L := ContinuousLinearMap.mul Real Real
  have h_int : Integrable fun v => fourierSMulRight L f v := by
    suffices Integrable fun v => ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [fourierSMulRight, neg_smul, neg_mul, Pi.smul_apply] using! this.smul (-2 * π * I)
    convert! ((ContinuousLinearMap.toSpanSingletonLIE Real
      E).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with _ v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply]; rw [ContinuousLinearMap.flip_apply]; rw [ContinuousLinearMap.mul_apply']; rw [one_mul]; rw [map_smul]
    exact congr_arg (fun x => v • x) (one_smul Real (f v)).symm
  convert! (VectorFourier.hasFDerivAt_fourierIntegral L hf hf'' w).hasDerivAt using 1
  rw [fourierIntegral_continuousLinearMap_apply' h_int]; rw [VectorFourier.fourierIntegral]; rw [fourier_real_eq]
  simp [fourierSMulRight, L, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', ← neg_mul, mul_smul]

中文:
引理 hasDerivAt_fourier
  证明: by
  have hf'' : Integrable (fun v : Real => ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using! hf'.norm
.flip let L := ContinuousLinearMap.mul Real Real
  have h_int : Integrable fun v => fourierSMulRight L f v := by
    suffices Integrable fun v => ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [fourierSMulRight, neg_smul, neg_mul, Pi.smul_apply] using! this.smul (-2 * π * I)
    convert! ((ContinuousLinearMap.toSpanSingletonLIE Real
      E).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with _ v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply]; rw [ContinuousLinearMap.flip_apply]; rw [ContinuousLinearMap.mul_apply']; rw [one_mul]; rw [map_smul]
    exact congr_arg (fun x => v • x) (one_smul Real (f v)).symm
  convert! (VectorFourier.hasFDerivAt_fourierIntegral L hf hf'' w).hasDerivAt using 1
  rw [fourierIntegral_continuousLinearMap_apply' h_int]; rw [VectorFourier.fourierIntegral]; rw [fourier_real_eq]
  simp [fourierSMulRight, L, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', ← neg_mul, mul_smul]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, ContinuousLinearMap.smulRight, ContinuousLinearMap.toSpanSingletonLIE, Integrable, Pi.smul_apply, convert, fourierSMulRight, h_int, integrable_comp, neg_mul, neg_smul, norm_smul, smulRight, smul_apply, this.smul, toContinuousLinearEquiv, toContinuousLinearEquiv.toContinuousLinearMap, toContinuousLinearMap, toSpanSingletonLIE
-/
lemma hasDerivAt_fourier
    {f : Real -> E} (hf : Integrable f) (hf' : Integrable (fun x : Real => x • f x)) (w : Real) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : Real => (-2 * π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : Real => ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using! hf'.norm
.flip let L := ContinuousLinearMap.mul Real Real
  have h_int : Integrable fun v => fourierSMulRight L f v := by
    suffices Integrable fun v => ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [fourierSMulRight, neg_smul, neg_mul, Pi.smul_apply] using! this.smul (-2 * π * I)
    convert! ((ContinuousLinearMap.toSpanSingletonLIE Real
      E).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with _ v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply]; rw [ContinuousLinearMap.flip_apply]; rw [ContinuousLinearMap.mul_apply']; rw [one_mul]; rw [map_smul]
    exact congr_arg (fun x => v • x) (one_smul Real (f v)).symm
  convert! (VectorFourier.hasFDerivAt_fourierIntegral L hf hf'' w).hasDerivAt using 1
  rw [fourierIntegral_continuousLinearMap_apply' h_int]; rw [VectorFourier.fourierIntegral]; rw [fourier_real_eq]
  simp [fourierSMulRight, L, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', ← neg_mul, mul_smul]

/--
theorem `deriv_fourier` / 定理 `deriv_fourier`

English:
theorem deriv_fourier
  proof: by
  ext x
  exact (hasDerivAt_fourier hf hf' x).deriv

中文:
定理 deriv_fourier
  证明: by
  ext x
  exact (hasDerivAt_fourier hf hf' x).deriv

Depends on / 依赖: hasDerivAt_fourier
-/
theorem deriv_fourier
    {f : Real -> E} (hf : Integrable f) (hf' : Integrable (fun x : Real => x • f x)) :
    deriv (𝓕 f) = 𝓕 (fun x : Real => (-2 * π * I * x) • f x) := by
  ext x
  exact (hasDerivAt_fourier hf hf' x).deriv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fourier_deriv` / 定理 `fourier_deriv`

English:
theorem fourier_deriv
  proof: by
  ext x
  have I : Integrable (fun x => fderiv Real f x) := by
    simpa only [← toSpanSingleton_deriv] using!
      (ContinuousLinearMap.smulRightL Real Real E 1).integrable_comp hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv Real f) x 1 := by
    simp only [fourier_continuousLinearMap_apply I, fderiv_apply_one_eq_deriv]
  rw [this]; rw [fourier_fderiv hf h'f I]
  simp only [fourierSMulRight_apply, neg_apply, innerSL_apply_apply Real, smul_smul,
    RCLike.inner_apply', conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, ← coe_smul]

中文:
定理 fourier_deriv
  证明: by
  ext x
  have I : Integrable (fun x => fderiv Real f x) := by
    simpa only [← toSpanSingleton_deriv] using!
      (ContinuousLinearMap.smulRightL Real Real E 1).integrable_comp hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv Real f) x 1 := by
    simp only [fourier_continuousLinearMap_apply I, fderiv_apply_one_eq_deriv]
  rw [this]; rw [fourier_fderiv hf h'f I]
  simp only [fourierSMulRight_apply, neg_apply, innerSL_apply_apply Real, smul_smul,
    RCLike.inner_apply', conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, ← coe_smul]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRightL, Integrable, RCLike, RCLike.inner_apply, conj_trivial, fderiv, fderiv_apply_one_eq_deriv, fourierSMulRight_apply, fourier_continuousLinearMap_apply, fourier_fderiv, innerSL_apply_apply, inner_apply, integrable_comp, mul_one, neg_apply, neg_m, neg_neg, neg_smul, smulRightL
-/
theorem fourier_deriv
    {f : Real -> E} (hf : Integrable f) (h'f : Differentiable Real f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : Real) => (2 * π * I * x) • (𝓕 f x) := by
  ext x
  have I : Integrable (fun x => fderiv Real f x) := by
    simpa only [← toSpanSingleton_deriv] using!
      (ContinuousLinearMap.smulRightL Real Real E 1).integrable_comp hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv Real f) x 1 := by
    simp only [fourier_continuousLinearMap_apply I, fderiv_apply_one_eq_deriv]
  rw [this]; rw [fourier_fderiv hf h'f I]
  simp only [fourierSMulRight_apply, neg_apply, innerSL_apply_apply Real, smul_smul,
    RCLike.inner_apply', conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, ← coe_smul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iteratedDeriv_fourier` / 定理 `iteratedDeriv_fourier`

English:
theorem iteratedDeriv_fourier
  statement: {f : Real -> E} {N : Nat∞} {n : Nat}
  proof: by
  ext x : 1
  have A (n : Nat) (hn : n <= N) : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) := by
    convert! (hf n hn).norm with x
    simp [norm_smul]
  have B : AEStronglyMeasurable f := by simpa using (hf 0 zero_le).1
  rw [iteratedDeriv]; rw [iteratedFDeriv_fourier A B hn]; rw [fourier_continuousMultilinearMap_apply (integrable_fourierPowSMulRight _ (A n hn) B)]; rw [fourier_eq]; rw [fourier_eq]
  congr with y
  suffices (-(2 * π * I)) ^ n • y ^ n • f y = (-(2 * π * I * y)) ^ n • f y by
    simpa [innerSL_apply_apply _]
  simp only [← neg_mul, ← coe_smul, smul_smul, mul_pow, ofReal_pow, mul_assoc]

中文:
定理 iteratedDeriv_fourier
  结论: {f : 实数 -> E} {N : 自然数∞} {n : 自然数}
  证明: by
  ext x : 1
  have A (n : Nat) (hn : n <= N) : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) := by
    convert! (hf n hn).norm with x
    simp [norm_smul]
  have B : AEStronglyMeasurable f := by simpa using (hf 0 zero_le).1
  rw [iteratedDeriv]; rw [iteratedFDeriv_fourier A B hn]; rw [fourier_continuousMultilinearMap_apply (integrable_fourierPowSMulRight _ (A n hn) B)]; rw [fourier_eq]; rw [fourier_eq]
  congr with y
  suffices (-(2 * π * I)) ^ n • y ^ n • f y = (-(2 * π * I * y)) ^ n • f y by
    simpa [innerSL_apply_apply _]
  simp only [← neg_mul, ← coe_smul, smul_smul, mul_pow, ofReal_pow, mul_assoc]

Depends on / 依赖: AEStronglyMeasurable, Integrable, convert, fourier_continuousMultilinearMap_apply, fourier_eq, innerSL_apply_apply, integrable_fourierPowSMulRight, iteratedDeriv, iteratedFDeriv_fourier, norm_smul, zero_le
-/
theorem iteratedDeriv_fourier {f : Real -> E} {N : Nat∞} {n : Nat}
    (hf : forall (n : Nat), n <= N -> Integrable (fun x => x ^ n • f x)) (hn : n <= N) :
    iteratedDeriv n (𝓕 f) = 𝓕 (fun x : Real => (-2 * π * I * x) ^ n • f x) := by
  ext x : 1
  have A (n : Nat) (hn : n <= N) : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) := by
    convert! (hf n hn).norm with x
    simp [norm_smul]
  have B : AEStronglyMeasurable f := by simpa using (hf 0 zero_le).1
  rw [iteratedDeriv]; rw [iteratedFDeriv_fourier A B hn]; rw [fourier_continuousMultilinearMap_apply (integrable_fourierPowSMulRight _ (A n hn) B)]; rw [fourier_eq]; rw [fourier_eq]
  congr with y
  suffices (-(2 * π * I)) ^ n • y ^ n • f y = (-(2 * π * I * y)) ^ n • f y by
    simpa [innerSL_apply_apply _]
  simp only [← neg_mul, ← coe_smul, smul_smul, mul_pow, ofReal_pow, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fourier_iteratedDeriv` / 定理 `fourier_iteratedDeriv`

English:
theorem fourier_iteratedDeriv
  statement: {f : Real -> E} {N : Nat∞} {n : Nat} (hf : ContDiff Real N f)
  proof: by
  ext x : 1
  have A : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  change 𝓕 (fun x => iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, ← fourier_continuousMultilinearMap_apply (A n hn),
    fourier_iteratedFDeriv hf A hn]
  simp [← coe_smul, smul_smul, ← mul_pow, innerSL_apply_apply Real]

中文:
定理 fourier_iteratedDeriv
  结论: {f : 实数 -> E} {N : 自然数∞} {n : 自然数} (hf : 连续可微 实数 N f)
  证明: by
  ext x : 1
  have A : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  change 𝓕 (fun x => iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, ← fourier_continuousMultilinearMap_apply (A n hn),
    fourier_iteratedFDeriv hf A hn]
  simp [← coe_smul, smul_smul, ← mul_pow, innerSL_apply_apply Real]

Depends on / 依赖: Integrable, LinearIsometryEquiv, LinearIsometryEquiv.integrable_comp_iff, coe_smul, fourier_continuousMultilinearMap_apply, fourier_iteratedFDeriv, innerSL_apply_apply, integrable_comp_iff, iteratedDeriv, iteratedFDeriv, iteratedFDeriv_eq_equiv_comp, mul_pow, simp_rw, smul_smul
-/
theorem fourier_iteratedDeriv {f : Real -> E} {N : Nat∞} {n : Nat} (hf : ContDiff Real N f)
    (h'f : forall (n : Nat), n <= N -> Integrable (iteratedDeriv n f)) (hn : n <= N) :
    𝓕 (iteratedDeriv n f) = fun (x : Real) => (2 * π * I * x) ^ n • (𝓕 f x) := by
  ext x : 1
  have A : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  change 𝓕 (fun x => iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, ← fourier_continuousMultilinearMap_apply (A n hn),
    fourier_iteratedFDeriv hf A hn]
  simp [← coe_smul, smul_smul, ← mul_pow, innerSL_apply_apply Real]

end Real
