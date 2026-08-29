/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Complex.Basic

/-! # Real differentiability of complex-differentiable functions

`HasDerivAt.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/

public section

assert_not_exists IsConformalMap Conformal

section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

open Complex

variable {e : Complex -> Complex} {e' : Complex} {z : Real}

/--
theorem `HasStrictDerivAt.real_of_complex` / 定理 `HasStrictDerivAt.real_of_complex`

English:
theorem HasStrictDerivAt.real_of_complex
  given: (h : HasStrictDerivAt e e' z)
  proof: by
  have A : HasStrictFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars Real
  have 

中文:
定理 HasStrictDerivAt.real_of_complex
  条件: (h : HasStrictDerivAt e e' z)
  证明: by
  have A : HasStrictFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars Real
  have 

Depends on / 依赖: B.comp, C.comp, ContinuousLinearMap, ContinuousLinearMap.smulRight, HasStrictFDerivAt, h.hasStrictFDerivAt.restrictScalars, hasStrictDerivAt, hasStrictFDerivAt, ofRealCLM, ofRealCLM.hasStrictFDerivAt, reCLM.hasStrictFDerivAt, restrictScalars, smulRight
-/
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : Real => (e x).re) e'.re z := by
  have A : HasStrictFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars Real
  have C : HasStrictFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasStrictFDerivAt
  simpa using (C.comp z (B.comp z A)).hasStrictDerivAt

/--
theorem `HasDerivAt.real_of_complex` / 定理 `HasDerivAt.real_of_complex`

English:
theorem HasDerivAt.real_of_complex
  given: (h : HasDerivAt e e' z)
  proof: by
  have A : HasFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars Real
  have C : HasFDerivAt re reCLM

中文:
定理 在点处可导.real_of_complex
  条件: (h : 在点处可导 e e' z)
  证明: by
  have A : HasFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars Real
  have C : HasFDerivAt re reCLM

Depends on / 依赖: B.comp, C.comp, ContinuousLinearMap, ContinuousLinearMap.smulRight, HasFDerivAt, h.hasFDerivAt.restrictScalars, hasDerivAt, hasFDerivAt, ofRealCLM, ofRealCLM.hasFDerivAt, reCLM.hasFDerivAt, restrictScalars, smulRight
-/
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : Real => (e x).re) e'.re z := by
  have A : HasFDerivAt ((↑) : Real -> Complex) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : Complex ->L[Complex] Complex).restrictScalars Real)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars Real
  have C : HasFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasFDerivAt
  simpa using! (C.comp z (B.comp z A)).hasDerivAt

/--
theorem `ContDiffAt.real_of_complex` / 定理 `ContDiffAt.real_of_complex`

English:
theorem ContDiffAt.real_of_complex
  given: {n : WithTop Nat∞} (h : ContDiffAt Complex n e z)
  proof: by
  have A : ContDiffAt Real n ((↑) : Real -> Complex) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt Real n e z := h.restrict_scalars Real
  have C : ContDiffAt Real n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)

中文:
定理 ContDiffAt.real_of_complex
  条件: {n : WithTop 自然数∞} (h : ContDiffAt 复形 n e z)
  证明: by
  have A : ContDiffAt Real n ((↑) : Real -> Complex) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt Real n e z := h.restrict_scalars Real
  have C : ContDiffAt Real n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)

Depends on / 依赖: B.comp, C.comp, ContDiffAt, contDiff, contDiffAt, h.restrict_scalars, ofRealCLM, ofRealCLM.contDiff.contDiffAt, reCLM.contDiff.contDiffAt, restrict_scalars
-/
theorem ContDiffAt.real_of_complex {n : WithTop Nat∞} (h : ContDiffAt Complex n e z) :
    ContDiffAt Real n (fun x : Real => (e x).re) z := by
  have A : ContDiffAt Real n ((↑) : Real -> Complex) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt Real n e z := h.restrict_scalars Real
  have C : ContDiffAt Real n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)

/--
theorem `ContDiff.real_of_complex` / 定理 `ContDiff.real_of_complex`

English:
theorem ContDiff.real_of_complex
  given: {n : WithTop Nat∞} (h : ContDiff Complex n e)
  proof: contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

中文:
定理 连续可微.real_of_complex
  条件: {n : WithTop 自然数∞} (h : 连续可微 复形 n e)
  证明: contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, h.contDiffAt.real_of_complex, real_of_complex
-/
theorem ContDiff.real_of_complex {n : WithTop Nat∞} (h : ContDiff Complex n e) :
    ContDiff Real n fun x : Real => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
theorem `HasStrictDerivAt.complexToReal_fderiv'` / 定理 `HasStrictDerivAt.complexToReal_fderiv'`

English:
theorem HasStrictDerivAt.complexToReal_fderiv'
  statement: {f : Complex -> E} {x : Complex} {f' : E}
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasStrictFDerivAt.restrictScalars Real

中文:
定理 HasStrictDerivAt.complexTo实数_fderiv'
  结论: {f : 复形 -> E} {x : 复形} {f' : E}
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasStrictFDerivAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasStrictFDerivAt.restrictScalars, hasStrictFDerivAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasStrictDerivAt.complexToReal_fderiv' {f : Complex -> E} {x : Complex} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasStrictFDerivAt.restrictScalars Real

/--
theorem `HasDerivAt.complexToReal_fderiv'` / 定理 `HasDerivAt.complexToReal_fderiv'`

English:
theorem HasDerivAt.complexToReal_fderiv'
  given: {f : Complex -> E} {x : Complex} {f' : E} (h : HasDerivAt f f' x)
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivAt.restrictScalars Real

中文:
定理 在点处可导.complexTo实数_fderiv'
  条件: {f : 复形 -> E} {x : 复形} {f' : E} (h : 在点处可导 f f' x)
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasFDerivAt.restrictScalars, hasFDerivAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasDerivAt.complexToReal_fderiv' {f : Complex -> E} {x : Complex} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivAt.restrictScalars Real

/--
theorem `HasDerivWithinAt.complexToReal_fderiv'` / 定理 `HasDerivWithinAt.complexToReal_fderiv'`

English:
theorem HasDerivWithinAt.complexToReal_fderiv'
  statement: {f : Complex -> E} {s : Set Complex} {x : Complex} {f' : E}
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivWithinAt.restrictScalars Real

中文:
定理 HasDerivWithinAt.complexTo实数_fderiv'
  结论: {f : 复形 -> E} {s : 集合 复形} {x : 复形} {f' : E}
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivWithinAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasFDerivWithinAt.restrictScalars, hasFDerivWithinAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasDerivWithinAt.complexToReal_fderiv' {f : Complex -> E} {s : Set Complex} {x : Complex} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reCLM.smulRight f' + I • imCLM.smulRight f') s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivWithinAt.restrictScalars Real

/--
theorem `HasStrictDerivAt.complexToReal_fderiv` / 定理 `HasStrictDerivAt.complexToReal_fderiv`

English:
theorem HasStrictDerivAt.complexToReal_fderiv
  given: {f : Complex -> Complex} {f' x : Complex} (h : HasStrictDerivAt f f' x)
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasStrictFDerivAt.restrictScalars Real

中文:
定理 HasStrictDerivAt.complexTo实数_fderiv
  条件: {f : 复形 -> 复形} {f' x : 复形} (h : HasStrictDerivAt f f' x)
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasStrictFDerivAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasStrictFDerivAt.restrictScalars, hasStrictFDerivAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasStrictDerivAt.complexToReal_fderiv {f : Complex -> Complex} {f' x : Complex} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : Complex ->L[Real] Complex)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasStrictFDerivAt.restrictScalars Real

/--
theorem `HasDerivAt.complexToReal_fderiv` / 定理 `HasDerivAt.complexToReal_fderiv`

English:
theorem HasDerivAt.complexToReal_fderiv
  given: {f : Complex -> Complex} {f' x : Complex} (h : HasDerivAt f f' x)
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivAt.restrictScalars Real

中文:
定理 在点处可导.complexTo实数_fderiv
  条件: {f : 复形 -> 复形} {f' x : 复形} (h : 在点处可导 f f' x)
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasFDerivAt.restrictScalars, hasFDerivAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasDerivAt.complexToReal_fderiv {f : Complex -> Complex} {f' x : Complex} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : Complex ->L[Real] Complex)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivAt.restrictScalars Real

/--
theorem `HasDerivWithinAt.complexToReal_fderiv` / 定理 `HasDerivWithinAt.complexToReal_fderiv`

English:
theorem HasDerivWithinAt.complexToReal_fderiv
  statement: {f : Complex -> Complex} {s : Set Complex} {f' x : Complex}
  proof: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivWithinAt.restrictScalars Real

中文:
定理 HasDerivWithinAt.complexTo实数_fderiv
  结论: {f : 复形 -> 复形} {s : 集合 复形} {f' x : 复形}
  证明: by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivWithinAt.restrictScalars Real

Depends on / 依赖: Complex.restrictScalars_toSpanSingleton, h.hasFDerivWithinAt.restrictScalars, hasFDerivWithinAt, restrictScalars, restrictScalars_toSpanSingleton
-/
theorem HasDerivWithinAt.complexToReal_fderiv {f : Complex -> Complex} {s : Set Complex} {f' x : Complex}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : Complex ->L[Real] Complex)) s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivWithinAt.restrictScalars Real

/--
theorem `HasDerivAt.comp_ofReal` / 定理 `HasDerivAt.comp_ofReal`

English:
theorem HasDerivAt.comp_ofReal
  given: (hf : HasDerivAt e e' ↑z)
  statement: HasDerivAt (fun y : Real => e ↑y) e' z
  proof: by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using! hf.comp z ofRealCLM.hasDerivAt

中文:
定理 在点处可导.comp_of实数
  条件: (hf : 在点处可导 e e' ↑z)
  结论: 在点处可导 (fun y : 实数 => e ↑y) e' z
  证明: by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using! hf.comp z ofRealCLM.hasDerivAt

Depends on / 依赖: hasDerivAt, hf.comp, mul_one, ofRealCLM, ofRealCLM.hasDerivAt, ofRealCLM_apply, ofReal_one
-/
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : Real => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using! hf.comp z ofRealCLM.hasDerivAt

/--
theorem `HasDerivAt.ofReal_comp` / 定理 `HasDerivAt.ofReal_comp`

English:
theorem HasDerivAt.ofReal_comp
  given: {f : Real -> Real} {u : Real} (hf : HasDerivAt f u z)
  proof: by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using!
    ofRealCLM.hasDerivAt.scomp z hf

中文:
定理 在点处可导.of实数_comp
  条件: {f : 实数 -> 实数} {u : 实数} (hf : 在点处可导 f u z)
  证明: by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using!
    ofRealCLM.hasDerivAt.scomp z hf

Depends on / 依赖: hasDerivAt, mul_one, ofRealCLM, ofRealCLM.hasDerivAt.scomp, ofRealCLM_apply, ofReal_one, real_smul
-/
theorem HasDerivAt.ofReal_comp {f : Real -> Real} {u : Real} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : Real => ↑(f y) : Real -> Complex) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using!
    ofRealCLM.hasDerivAt.scomp z hf

/--
theorem `HasDerivWithinAt.ofReal_comp` / 定理 `HasDerivWithinAt.ofReal_comp`

English:
theorem HasDerivWithinAt.ofReal_comp
  statement: {f : Real -> Real} {s : Set Real} {u : Real}
  proof: by
  simpa only [Function.comp_apply, ofRealCLM_apply] using!
    ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt z hf

@[fun_prop]

中文:
定理 HasDerivWithinAt.of实数_comp
  结论: {f : 实数 -> 实数} {s : 集合 实数} {u : 实数}
  证明: by
  simpa only [Function.comp_apply, ofRealCLM_apply] using!
    ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt z hf

@[fun_prop]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_hasDerivWithinAt, hasFDerivAt, ofRealCLM, ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt, ofRealCLM_apply
-/
theorem HasDerivWithinAt.ofReal_comp {f : Real -> Real} {s : Set Real} {u : Real}
    (hf : HasDerivWithinAt f u s z) : HasDerivWithinAt (fun y : Real => ↑(f y) : Real -> Complex) u s z := by
  simpa only [Function.comp_apply, ofRealCLM_apply] using!
    ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt z hf

@[fun_prop]
/--
lemma `Complex.differentiable_re` / 引理 `Complex.differentiable_re`

English:
lemma Complex.differentiable_re
  statement: Differentiable Real Complex.re
  proof: reCLM.differentiable

@[fun_prop]

中文:
引理 复形.differentiable_re
  结论: 可微 实数 复形.re
  证明: reCLM.differentiable

@[fun_prop]

Depends on / 依赖: differentiable, reCLM.differentiable
-/
lemma Complex.differentiable_re : Differentiable Real Complex.re := reCLM.differentiable

@[fun_prop]
/--
lemma `Complex.differentiable_im` / 引理 `Complex.differentiable_im`

English:
lemma Complex.differentiable_im
  statement: Differentiable Real Complex.im
  proof: imCLM.differentiable

@[fun_prop]

中文:
引理 复形.differentiable_im
  结论: 可微 实数 复形.im
  证明: imCLM.differentiable

@[fun_prop]

Depends on / 依赖: differentiable, imCLM.differentiable
-/
lemma Complex.differentiable_im : Differentiable Real Complex.im := imCLM.differentiable

@[fun_prop]
/--
lemma `Complex.differentiable_ofReal` / 引理 `Complex.differentiable_ofReal`

English:
lemma Complex.differentiable_ofReal
  statement: Differentiable Real Complex.ofReal
  proof: ofRealCLM.differentiable

中文:
引理 复形.differentiable_of实数
  结论: 可微 实数 复形.of实数
  证明: ofRealCLM.differentiable

Depends on / 依赖: differentiable, ofRealCLM, ofRealCLM.differentiable
-/
lemma Complex.differentiable_ofReal : Differentiable Real Complex.ofReal := ofRealCLM.differentiable

open ComplexConjugate in
@[fun_prop]
/--
lemma `Complex.differentiable_conj` / 引理 `Complex.differentiable_conj`

English:
lemma Complex.differentiable_conj
  statement: Differentiable Real (conj : Complex -> Complex)
  proof: conjCLE.differentiable

中文:
引理 复形.differentiable_conj
  结论: 可微 实数 (conj : 复形 -> 复形)
  证明: conjCLE.differentiable

Depends on / 依赖: conjCLE, conjCLE.differentiable, differentiable
-/
lemma Complex.differentiable_conj : Differentiable Real (conj : Complex -> Complex) := conjCLE.differentiable

variable {f : Complex -> E} {s : Set Complex} {z : Complex}

@[fun_prop]
/--
lemma `Differentiable.real_of_complex` / 引理 `Differentiable.real_of_complex`

English:
lemma Differentiable.real_of_complex
  given: (hf : Differentiable Complex f)
  statement: Differentiable Real f
  proof: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

中文:
引理 可微.real_of_complex
  条件: (hf : 可微 复形 f)
  结论: 可微 实数 f
  证明: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

Depends on / 依赖: hf.restrictScalars, restrictScalars
-/
lemma Differentiable.real_of_complex (hf : Differentiable Complex f) : Differentiable Real f :=
  hf.restrictScalars (𝕜 := Real)

@[fun_prop]
/--
lemma `DifferentiableAt.real_of_complex` / 引理 `DifferentiableAt.real_of_complex`

English:
lemma DifferentiableAt.real_of_complex
  given: (hf : DifferentiableAt Complex f z)
  statement: DifferentiableAt Real f z
  proof: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

中文:
引理 DifferentiableAt.real_of_complex
  条件: (hf : DifferentiableAt 复形 f z)
  结论: DifferentiableAt 实数 f z
  证明: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

Depends on / 依赖: hf.restrictScalars, restrictScalars
-/
lemma DifferentiableAt.real_of_complex (hf : DifferentiableAt Complex f z) : DifferentiableAt Real f z :=
  hf.restrictScalars (𝕜 := Real)

@[fun_prop]
/--
lemma `DifferentiableWithinAt.real_of_complex` / 引理 `DifferentiableWithinAt.real_of_complex`

English:
lemma DifferentiableWithinAt.real_of_complex
  given: (hf : DifferentiableWithinAt Complex f s z)
  proof: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

中文:
引理 DifferentiableWithinAt.real_of_complex
  条件: (hf : DifferentiableWithinAt 复形 f s z)
  证明: hf.restrictScalars (𝕜 := Real)

@[fun_prop]

Depends on / 依赖: hf.restrictScalars, restrictScalars
-/
lemma DifferentiableWithinAt.real_of_complex (hf : DifferentiableWithinAt Complex f s z) :
    DifferentiableWithinAt Real f s z :=
  hf.restrictScalars (𝕜 := Real)

@[fun_prop]
/--
lemma `DifferentiableOn.real_of_complex` / 引理 `DifferentiableOn.real_of_complex`

English:
lemma DifferentiableOn.real_of_complex
  given: (hf : DifferentiableOn Complex f s)
  statement: DifferentiableOn Real f s
  proof: hf.restrictScalars (𝕜 := Real)

中文:
引理 DifferentiableOn.real_of_complex
  条件: (hf : DifferentiableOn 复形 f s)
  结论: DifferentiableOn 实数 f s
  证明: hf.restrictScalars (𝕜 := Real)

Depends on / 依赖: hf.restrictScalars, restrictScalars
-/
lemma DifferentiableOn.real_of_complex (hf : DifferentiableOn Complex f s) : DifferentiableOn Real f s :=
  hf.restrictScalars (𝕜 := Real)

end RealDerivOfComplex
