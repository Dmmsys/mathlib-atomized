/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Order.Monotone.Odd
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differentiability of hyperbolic trigonometric functions

## Main statements

The differentiability of the hyperbolic trigonometric functions is proved, and their derivatives are
computed.

## Tags

sinh, cosh, tanh
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/--
theorem `hasStrictDerivAt_sinh` / 定理 `hasStrictDerivAt_sinh`

English:
theorem hasStrictDerivAt_sinh
  given: (x : Complex)
  statement: HasStrictDerivAt sinh (cosh x) x
  proof: by
  simp only [cosh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]; rw [neg_neg]

中文:
定理 hasStrictDerivAt_sinh
  条件: (x : 复形)
  结论: HasStrictDerivAt sinh (cosh x) x
  证明: by
  simp only [cosh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]; rw [neg_neg]

Depends on / 依赖: convert, div_eq_mul_inv, fun_neg, fun_neg.cexp, hasStrictDerivAt_exp, hasStrictDerivAt_id, mul_const, mul_neg_one, neg_neg, sub_eq_add_neg
-/
theorem hasStrictDerivAt_sinh (x : Complex) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]; rw [neg_neg]

/--
theorem `hasDerivAt_sinh` / 定理 `hasDerivAt_sinh`

English:
theorem hasDerivAt_sinh
  given: (x : Complex)
  statement: HasDerivAt sinh (cosh x) x
  proof: (hasStrictDerivAt_sinh x).hasDerivAt

中文:
定理 hasDerivAt_sinh
  条件: (x : 复形)
  结论: 在点处可导 sinh (cosh x) x
  证明: (hasStrictDerivAt_sinh x).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_sinh
-/
theorem hasDerivAt_sinh (x : Complex) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt

/--
theorem `isEquivalent_sinh` / 定理 `isEquivalent_sinh`

English:
theorem isEquivalent_sinh
  statement: sinh ~[𝓝 0] id
  proof: by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]

中文:
定理 isEquivalent_sinh
  结论: sinh ~[𝓝 0] id
  证明: by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]

Depends on / 依赖: hasDerivAt_sinh, isLittleO
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
/--
theorem `contDiff_sinh` / 定理 `contDiff_sinh`

English:
theorem contDiff_sinh
  given: {n}
  statement: ContDiff Complex n sinh
  proof: (contDiff_exp.sub contDiff_neg.cexp).div_const _

@[simp]

中文:
定理 contDiff_sinh
  条件: {n}
  结论: 连续可微 复形 n sinh
  证明: (contDiff_exp.sub contDiff_neg.cexp).div_const _

@[simp]

Depends on / 依赖: contDiff_exp, contDiff_exp.sub, contDiff_neg, contDiff_neg.cexp, div_const
-/
theorem contDiff_sinh {n} : ContDiff Complex n sinh :=
  (contDiff_exp.sub contDiff_neg.cexp).div_const _

@[simp]
/--
theorem `differentiable_sinh` / 定理 `differentiable_sinh`

English:
theorem differentiable_sinh
  statement: Differentiable Complex sinh
  proof: fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]

中文:
定理 differentiable_sinh
  结论: 可微 复形 sinh
  证明: fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]

Depends on / 依赖: Discrete, Discrete.natIso, differentiableAt, hasDerivAt_sinh, infer_instance, natIso
-/
theorem differentiable_sinh : Differentiable Complex sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
/--
theorem `differentiableAt_sinh` / 定理 `differentiableAt_sinh`

English:
theorem differentiableAt_sinh
  given: {x : Complex}
  statement: DifferentiableAt Complex sinh x
  proof: differentiable_sinh x

中文:
定理 differentiableAt_sinh
  条件: {x : 复形}
  结论: DifferentiableAt 复形 sinh x
  证明: differentiable_sinh x

Depends on / 依赖: differentiable_sinh
-/
theorem differentiableAt_sinh {x : Complex} : DifferentiableAt Complex sinh x :=
  differentiable_sinh x

/-- The function `Complex.sinh` is complex analytic. -/
@[fun_prop]
/--
lemma `analyticAt_sinh` / 引理 `analyticAt_sinh`

English:
lemma analyticAt_sinh
  given: {x : Complex}
  statement: AnalyticAt Complex sinh x
  proof: contDiff_sinh.contDiffAt.analyticAt

中文:
引理 analyticAt_sinh
  条件: {x : 复形}
  结论: AnalyticAt 复形 sinh x
  证明: contDiff_sinh.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_sinh, contDiff_sinh.contDiffAt.analyticAt
-/
lemma analyticAt_sinh {x : Complex} : AnalyticAt Complex sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_sinh` / 引理 `analyticWithinAt_sinh`

English:
lemma analyticWithinAt_sinh
  given: {x : Complex} {s : Set Complex}
  statement: AnalyticWithinAt Complex sinh s x
  proof: contDiff_sinh.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_sinh
  条件: {x : 复形} {s : 集合 复形}
  结论: AnalyticWithinAt 复形 sinh s x
  证明: contDiff_sinh.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_sinh, contDiff_sinh.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_sinh {x : Complex} {s : Set Complex} : AnalyticWithinAt Complex sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_sinh` / 定理 `analyticOnNhd_sinh`

English:
theorem analyticOnNhd_sinh
  given: {s : Set Complex}
  statement: AnalyticOnNhd Complex sinh s
  proof: fun _ _ => analyticAt_sinh

中文:
定理 analyticOnNhd_sinh
  条件: {s : 集合 复形}
  结论: AnalyticOnNhd 复形 sinh s
  证明: fun _ _ => analyticAt_sinh

Depends on / 依赖: analyticAt_sinh
-/
theorem analyticOnNhd_sinh {s : Set Complex} : AnalyticOnNhd Complex sinh s :=
  fun _ _ => analyticAt_sinh

/--
lemma `analyticOn_sinh` / 引理 `analyticOn_sinh`

English:
lemma analyticOn_sinh
  given: {s : Set Complex}
  statement: AnalyticOn Complex sinh s
  proof: contDiff_sinh.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_sinh
  条件: {s : 集合 复形}
  结论: AnalyticOn 复形 sinh s
  证明: contDiff_sinh.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_sinh, contDiff_sinh.contDiffOn.analyticOn
-/
lemma analyticOn_sinh {s : Set Complex} : AnalyticOn Complex sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_sinh` / 定理 `deriv_sinh`

English:
theorem deriv_sinh
  statement: deriv sinh = cosh
  proof: funext fun x => (hasDerivAt_sinh x).deriv

中文:
定理 deriv_sinh
  结论: deriv sinh = cosh
  证明: funext fun x => (hasDerivAt_sinh x).deriv

Depends on / 依赖: hasDerivAt_sinh
-/
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/--
theorem `hasStrictDerivAt_cosh` / 定理 `hasStrictDerivAt_cosh`

English:
theorem hasStrictDerivAt_cosh
  given: (x : Complex)
  statement: HasStrictDerivAt cosh (sinh x) x
  proof: by
  simp only [sinh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]

中文:
定理 hasStrictDerivAt_cosh
  条件: (x : 复形)
  结论: HasStrictDerivAt cosh (sinh x) x
  证明: by
  simp only [sinh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]

Depends on / 依赖: convert, div_eq_mul_inv, fun_neg, fun_neg.cexp, hasStrictDerivAt_exp, hasStrictDerivAt_id, mul_const, mul_neg_one, sub_eq_add_neg
-/
theorem hasStrictDerivAt_cosh (x : Complex) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [sinh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : Complex)⁻¹ using 1
  rw [id]; rw [mul_neg_one]; rw [sub_eq_add_neg]

/--
theorem `hasDerivAt_cosh` / 定理 `hasDerivAt_cosh`

English:
theorem hasDerivAt_cosh
  given: (x : Complex)
  statement: HasDerivAt cosh (sinh x) x
  proof: (hasStrictDerivAt_cosh x).hasDerivAt

@[fun_prop]

中文:
定理 hasDerivAt_cosh
  条件: (x : 复形)
  结论: 在点处可导 cosh (sinh x) x
  证明: (hasStrictDerivAt_cosh x).hasDerivAt

@[fun_prop]

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_cosh
-/
theorem hasDerivAt_cosh (x : Complex) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt

@[fun_prop]
/--
theorem `contDiff_cosh` / 定理 `contDiff_cosh`

English:
theorem contDiff_cosh
  given: {n}
  statement: ContDiff Complex n cosh
  proof: (contDiff_exp.add contDiff_neg.cexp).div_const _

@[simp]

中文:
定理 contDiff_cosh
  条件: {n}
  结论: 连续可微 复形 n cosh
  证明: (contDiff_exp.add contDiff_neg.cexp).div_const _

@[simp]

Depends on / 依赖: contDiff_exp, contDiff_exp.add, contDiff_neg, contDiff_neg.cexp, div_const
-/
theorem contDiff_cosh {n} : ContDiff Complex n cosh :=
  (contDiff_exp.add contDiff_neg.cexp).div_const _

@[simp]
/--
theorem `differentiable_cosh` / 定理 `differentiable_cosh`

English:
theorem differentiable_cosh
  statement: Differentiable Complex cosh
  proof: fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]

中文:
定理 differentiable_cosh
  结论: 可微 复形 cosh
  证明: fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_cosh
-/
theorem differentiable_cosh : Differentiable Complex cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
/--
theorem `differentiableAt_cosh` / 定理 `differentiableAt_cosh`

English:
theorem differentiableAt_cosh
  given: {x : Complex}
  statement: DifferentiableAt Complex cosh x
  proof: differentiable_cosh x

中文:
定理 differentiableAt_cosh
  条件: {x : 复形}
  结论: DifferentiableAt 复形 cosh x
  证明: differentiable_cosh x

Depends on / 依赖: differentiable_cosh
-/
theorem differentiableAt_cosh {x : Complex} : DifferentiableAt Complex cosh x :=
  differentiable_cosh x

/-- The function `Complex.cosh` is complex analytic. -/
@[fun_prop]
/--
lemma `analyticAt_cosh` / 引理 `analyticAt_cosh`

English:
lemma analyticAt_cosh
  given: {x : Complex}
  statement: AnalyticAt Complex cosh x
  proof: contDiff_cosh.contDiffAt.analyticAt

中文:
引理 analyticAt_cosh
  条件: {x : 复形}
  结论: AnalyticAt 复形 cosh x
  证明: contDiff_cosh.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_cosh, contDiff_cosh.contDiffAt.analyticAt
-/
lemma analyticAt_cosh {x : Complex} : AnalyticAt Complex cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_cosh` / 引理 `analyticWithinAt_cosh`

English:
lemma analyticWithinAt_cosh
  given: {x : Complex} {s : Set Complex}
  statement: AnalyticWithinAt Complex cosh s x
  proof: contDiff_cosh.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_cosh
  条件: {x : 复形} {s : 集合 复形}
  结论: AnalyticWithinAt 复形 cosh s x
  证明: contDiff_cosh.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_cosh, contDiff_cosh.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_cosh {x : Complex} {s : Set Complex} : AnalyticWithinAt Complex cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_cosh` / 定理 `analyticOnNhd_cosh`

English:
theorem analyticOnNhd_cosh
  given: {s : Set Complex}
  statement: AnalyticOnNhd Complex cosh s
  proof: fun _ _ => analyticAt_cosh

中文:
定理 analyticOnNhd_cosh
  条件: {s : 集合 复形}
  结论: AnalyticOnNhd 复形 cosh s
  证明: fun _ _ => analyticAt_cosh

Depends on / 依赖: analyticAt_cosh
-/
theorem analyticOnNhd_cosh {s : Set Complex} : AnalyticOnNhd Complex cosh s :=
  fun _ _ => analyticAt_cosh

/--
lemma `analyticOn_cosh` / 引理 `analyticOn_cosh`

English:
lemma analyticOn_cosh
  given: {s : Set Complex}
  statement: AnalyticOn Complex cosh s
  proof: contDiff_cosh.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_cosh
  条件: {s : 集合 复形}
  结论: AnalyticOn 复形 cosh s
  证明: contDiff_cosh.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_cosh, contDiff_cosh.contDiffOn.analyticOn
-/
lemma analyticOn_cosh {s : Set Complex} : AnalyticOn Complex cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_cosh` / 定理 `deriv_cosh`

English:
theorem deriv_cosh
  statement: deriv cosh = sinh
  proof: funext fun x => (hasDerivAt_cosh x).deriv

中文:
定理 deriv_cosh
  结论: deriv cosh = sinh
  证明: funext fun x => (hasDerivAt_cosh x).deriv

Depends on / 依赖: hasDerivAt_cosh
-/
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variable {f : Complex -> Complex} {f' x : Complex} {s : Set Complex}


/--
theorem `HasStrictDerivAt.ccosh` / 定理 `HasStrictDerivAt.ccosh`

English:
theorem HasStrictDerivAt.ccosh
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_cosh (f x)).comp x hf

中文:
定理 HasStrictDerivAt.ccosh
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_cosh (f x)).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cosh, hasStrictDerivAt_cosh
-/
theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp x hf

/--
theorem `HasDerivAt.ccosh` / 定理 `HasDerivAt.ccosh`

English:
theorem HasDerivAt.ccosh
  given: (hf : HasDerivAt f f' x)
  proof: (Complex.hasDerivAt_cosh (f x)).comp x hf

中文:
定理 在点处可导.ccosh
  条件: (hf : 在点处可导 f f' x)
  证明: (Complex.hasDerivAt_cosh (f x)).comp x hf

Depends on / 依赖: Complex.hasDerivAt_cosh, hasDerivAt_cosh
-/
theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp x hf

/--
theorem `HasDerivWithinAt.ccosh` / 定理 `HasDerivWithinAt.ccosh`

English:
theorem HasDerivWithinAt.ccosh
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.ccosh
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_cosh, comp_hasDerivWithinAt, hasDerivAt_cosh
-/
theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_ccosh` / 定理 `derivWithin_ccosh`

English:
theorem derivWithin_ccosh
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasDerivWithinAt.ccosh.derivWithin hxs

@[simp]

中文:
定理 derivWithin_ccosh
  条件: (hf : DifferentiableWithinAt 复形 f s x) (hxs : UniqueDiffWithinAt 复形 s x)
  证明: hf.hasDerivWithinAt.ccosh.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.ccosh.derivWithin
-/
theorem derivWithin_ccosh (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccosh.derivWithin hxs

@[simp]
/--
theorem `deriv_ccosh` / 定理 `deriv_ccosh`

English:
theorem deriv_ccosh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasDerivAt.ccosh.deriv

中文:
定理 deriv_ccosh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasDerivAt.ccosh.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.ccosh.deriv
-/
theorem deriv_ccosh (hc : DifferentiableAt Complex f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.hasDerivAt.ccosh.deriv


/--
theorem `HasStrictDerivAt.csinh` / 定理 `HasStrictDerivAt.csinh`

English:
theorem HasStrictDerivAt.csinh
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_sinh (f x)).comp x hf

中文:
定理 HasStrictDerivAt.csinh
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_sinh (f x)).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_sinh, hasStrictDerivAt_sinh
-/
theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp x hf

/--
theorem `HasDerivAt.csinh` / 定理 `HasDerivAt.csinh`

English:
theorem HasDerivAt.csinh
  given: (hf : HasDerivAt f f' x)
  proof: (Complex.hasDerivAt_sinh (f x)).comp x hf

中文:
定理 在点处可导.csinh
  条件: (hf : 在点处可导 f f' x)
  证明: (Complex.hasDerivAt_sinh (f x)).comp x hf

Depends on / 依赖: Complex.hasDerivAt_sinh, hasDerivAt_sinh
-/
theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp x hf

/--
theorem `HasDerivWithinAt.csinh` / 定理 `HasDerivWithinAt.csinh`

English:
theorem HasDerivWithinAt.csinh
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.csinh
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_sinh, comp_hasDerivWithinAt, hasDerivAt_sinh
-/
theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_csinh` / 定理 `derivWithin_csinh`

English:
theorem derivWithin_csinh
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasDerivWithinAt.csinh.derivWithin hxs

@[simp]

中文:
定理 derivWithin_csinh
  条件: (hf : DifferentiableWithinAt 复形 f s x) (hxs : UniqueDiffWithinAt 复形 s x)
  证明: hf.hasDerivWithinAt.csinh.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.csinh.derivWithin
-/
theorem derivWithin_csinh (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csinh.derivWithin hxs

@[simp]
/--
theorem `deriv_csinh` / 定理 `deriv_csinh`

English:
theorem deriv_csinh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasDerivAt.csinh.deriv

中文:
定理 deriv_csinh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasDerivAt.csinh.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.csinh.deriv
-/
theorem deriv_csinh (hc : DifferentiableAt Complex f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.hasDerivAt.csinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {f : E -> Complex} {f' : StrongDual Complex E}
  {x : E} {s : Set E}


/--
theorem `HasStrictFDerivAt.ccosh` / 定理 `HasStrictFDerivAt.ccosh`

English:
theorem HasStrictFDerivAt.ccosh
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.ccosh
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cosh, comp_hasStrictFDerivAt, hasStrictDerivAt_cosh
-/
theorem HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.ccosh` / 定理 `HasFDerivAt.ccosh`

English:
theorem HasFDerivAt.ccosh
  given: (hf : HasFDerivAt f f' x)
  proof: (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.ccosh
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Complex.hasDerivAt_cosh, comp_hasFDerivAt, hasDerivAt_cosh
-/
theorem HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.ccosh` / 定理 `HasFDerivWithinAt.ccosh`

English:
theorem HasFDerivWithinAt.ccosh
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.ccosh
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_cosh, comp_hasFDerivWithinAt, hasDerivAt_cosh
-/
theorem HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.ccosh` / 定理 `DifferentiableWithinAt.ccosh`

English:
theorem DifferentiableWithinAt.ccosh
  given: (hf : DifferentiableWithinAt Complex f s x)
  proof: hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.ccosh
  条件: (hf : DifferentiableWithinAt 复形 f s x)
  证明: hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.ccosh.differentiableWithinAt
-/
theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt Complex f s x) :
    DifferentiableWithinAt Complex (fun x => Complex.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.ccosh` / 定理 `DifferentiableAt.ccosh`

English:
theorem DifferentiableAt.ccosh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.ccosh.differentiableAt

中文:
定理 DifferentiableAt.ccosh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasFDerivAt.ccosh.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.ccosh.differentiableAt
-/
theorem DifferentiableAt.ccosh (hc : DifferentiableAt Complex f x) :
    DifferentiableAt Complex (fun x => Complex.cosh (f x)) x :=
  hc.hasFDerivAt.ccosh.differentiableAt

/--
theorem `DifferentiableOn.ccosh` / 定理 `DifferentiableOn.ccosh`

English:
theorem DifferentiableOn.ccosh
  given: (hc : DifferentiableOn Complex f s)
  proof: fun x h => (hc x h).ccosh

@[simp, fun_prop]

中文:
定理 DifferentiableOn.ccosh
  条件: (hc : DifferentiableOn 复形 f s)
  证明: fun x h => (hc x h).ccosh

@[simp, fun_prop]
-/
theorem DifferentiableOn.ccosh (hc : DifferentiableOn Complex f s) :
    DifferentiableOn Complex (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh

@[simp, fun_prop]
/--
theorem `Differentiable.ccosh` / 定理 `Differentiable.ccosh`

English:
theorem Differentiable.ccosh
  given: (hc : Differentiable Complex f)
  proof: fun x => (hc x).ccosh

中文:
定理 可微.ccosh
  条件: (hc : 可微 复形 f)
  证明: fun x => (hc x).ccosh
-/
theorem Differentiable.ccosh (hc : Differentiable Complex f) :
    Differentiable Complex fun x => Complex.cosh (f x) := fun x => (hc x).ccosh

/--
theorem `fderivWithin_ccosh` / 定理 `fderivWithin_ccosh`

English:
theorem fderivWithin_ccosh
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_ccosh
  条件: (hf : DifferentiableWithinAt 复形 f s x) (hxs : UniqueDiffWithinAt 复形 s x)
  证明: hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.ccosh.fderivWithin
-/
theorem fderivWithin_ccosh (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    fderivWithin Complex (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin Complex f s x :=
  hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

@[simp]
/--
theorem `fderiv_ccosh` / 定理 `fderiv_ccosh`

English:
theorem fderiv_ccosh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.ccosh.fderiv

中文:
定理 fderiv_ccosh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasFDerivAt.ccosh.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.ccosh.fderiv
-/
theorem fderiv_ccosh (hc : DifferentiableAt Complex f x) :
    fderiv Complex (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv Complex f x :=
  hc.hasFDerivAt.ccosh.fderiv

/--
theorem `ContDiff.ccosh` / 定理 `ContDiff.ccosh`

English:
theorem ContDiff.ccosh
  given: {n} (h : ContDiff Complex n f)
  statement: ContDiff Complex n fun x => Complex.cosh (f x)
  proof: Complex.contDiff_cosh.comp h

中文:
定理 连续可微.ccosh
  条件: {n} (h : 连续可微 复形 n f)
  结论: 连续可微 复形 n fun x => 复形.cosh (f x)
  证明: Complex.contDiff_cosh.comp h

Depends on / 依赖: Complex.contDiff_cosh.comp, contDiff_cosh
-/
theorem ContDiff.ccosh {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x => Complex.cosh (f x) :=
  Complex.contDiff_cosh.comp h

/--
theorem `ContDiffAt.ccosh` / 定理 `ContDiffAt.ccosh`

English:
theorem ContDiffAt.ccosh
  given: {n} (hf : ContDiffAt Complex n f x)
  proof: Complex.contDiff_cosh.contDiffAt.comp x hf

中文:
定理 ContDiffAt.ccosh
  条件: {n} (hf : ContDiffAt 复形 n f x)
  证明: Complex.contDiff_cosh.contDiffAt.comp x hf

Depends on / 依赖: Complex.contDiff_cosh.contDiffAt.comp, contDiffAt, contDiff_cosh
-/
theorem ContDiffAt.ccosh {n} (hf : ContDiffAt Complex n f x) :
    ContDiffAt Complex n (fun x => Complex.cosh (f x)) x :=
  Complex.contDiff_cosh.contDiffAt.comp x hf

/--
theorem `ContDiffOn.ccosh` / 定理 `ContDiffOn.ccosh`

English:
theorem ContDiffOn.ccosh
  given: {n} (hf : ContDiffOn Complex n f s)
  proof: Complex.contDiff_cosh.comp_contDiffOn hf

中文:
定理 ContDiffOn.ccosh
  条件: {n} (hf : ContDiffOn 复形 n f s)
  证明: Complex.contDiff_cosh.comp_contDiffOn hf

Depends on / 依赖: Complex.contDiff_cosh.comp_contDiffOn, comp_contDiffOn, contDiff_cosh
-/
theorem ContDiffOn.ccosh {n} (hf : ContDiffOn Complex n f s) :
    ContDiffOn Complex n (fun x => Complex.cosh (f x)) s :=
  Complex.contDiff_cosh.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.ccosh` / 定理 `ContDiffWithinAt.ccosh`

English:
theorem ContDiffWithinAt.ccosh
  given: {n} (hf : ContDiffWithinAt Complex n f s x)
  proof: Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.ccosh
  条件: {n} (hf : ContDiffWithinAt 复形 n f s x)
  证明: Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_cosh
-/
theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt Complex n f s x) :
    ContDiffWithinAt Complex n (fun x => Complex.cosh (f x)) s x :=
  Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf


/--
theorem `HasStrictFDerivAt.csinh` / 定理 `HasStrictFDerivAt.csinh`

English:
theorem HasStrictFDerivAt.csinh
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.csinh
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_sinh, comp_hasStrictFDerivAt, hasStrictDerivAt_sinh
-/
theorem HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.csinh` / 定理 `HasFDerivAt.csinh`

English:
theorem HasFDerivAt.csinh
  given: (hf : HasFDerivAt f f' x)
  proof: (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.csinh
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Complex.hasDerivAt_sinh, comp_hasFDerivAt, hasDerivAt_sinh
-/
theorem HasFDerivAt.csinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.csinh` / 定理 `HasFDerivWithinAt.csinh`

English:
theorem HasFDerivWithinAt.csinh
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.csinh
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_sinh, comp_hasFDerivWithinAt, hasDerivAt_sinh
-/
theorem HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.csinh` / 定理 `DifferentiableWithinAt.csinh`

English:
theorem DifferentiableWithinAt.csinh
  given: (hf : DifferentiableWithinAt Complex f s x)
  proof: hf.hasFDerivWithinAt.csinh.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.csinh
  条件: (hf : DifferentiableWithinAt 复形 f s x)
  证明: hf.hasFDerivWithinAt.csinh.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.csinh.differentiableWithinAt
-/
theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt Complex f s x) :
    DifferentiableWithinAt Complex (fun x => Complex.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.csinh.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.csinh` / 定理 `DifferentiableAt.csinh`

English:
theorem DifferentiableAt.csinh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.csinh.differentiableAt

中文:
定理 DifferentiableAt.csinh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasFDerivAt.csinh.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.csinh.differentiableAt
-/
theorem DifferentiableAt.csinh (hc : DifferentiableAt Complex f x) :
    DifferentiableAt Complex (fun x => Complex.sinh (f x)) x :=
  hc.hasFDerivAt.csinh.differentiableAt

/--
theorem `DifferentiableOn.csinh` / 定理 `DifferentiableOn.csinh`

English:
theorem DifferentiableOn.csinh
  given: (hc : DifferentiableOn Complex f s)
  proof: fun x h => (hc x h).csinh

@[simp, fun_prop]

中文:
定理 DifferentiableOn.csinh
  条件: (hc : DifferentiableOn 复形 f s)
  证明: fun x h => (hc x h).csinh

@[simp, fun_prop]
-/
theorem DifferentiableOn.csinh (hc : DifferentiableOn Complex f s) :
    DifferentiableOn Complex (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh

@[simp, fun_prop]
/--
theorem `Differentiable.csinh` / 定理 `Differentiable.csinh`

English:
theorem Differentiable.csinh
  given: (hc : Differentiable Complex f)
  proof: fun x => (hc x).csinh

中文:
定理 可微.csinh
  条件: (hc : 可微 复形 f)
  证明: fun x => (hc x).csinh
-/
theorem Differentiable.csinh (hc : Differentiable Complex f) :
    Differentiable Complex fun x => Complex.sinh (f x) := fun x => (hc x).csinh

/--
theorem `fderivWithin_csinh` / 定理 `fderivWithin_csinh`

English:
theorem fderivWithin_csinh
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasFDerivWithinAt.csinh.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_csinh
  条件: (hf : DifferentiableWithinAt 复形 f s x) (hxs : UniqueDiffWithinAt 复形 s x)
  证明: hf.hasFDerivWithinAt.csinh.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.csinh.fderivWithin
-/
theorem fderivWithin_csinh (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    fderivWithin Complex (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin Complex f s x :=
  hf.hasFDerivWithinAt.csinh.fderivWithin hxs

@[simp]
/--
theorem `fderiv_csinh` / 定理 `fderiv_csinh`

English:
theorem fderiv_csinh
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.csinh.fderiv

中文:
定理 fderiv_csinh
  条件: (hc : DifferentiableAt 复形 f x)
  证明: hc.hasFDerivAt.csinh.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.csinh.fderiv
-/
theorem fderiv_csinh (hc : DifferentiableAt Complex f x) :
    fderiv Complex (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv Complex f x :=
  hc.hasFDerivAt.csinh.fderiv

/--
theorem `ContDiff.csinh` / 定理 `ContDiff.csinh`

English:
theorem ContDiff.csinh
  given: {n} (h : ContDiff Complex n f)
  statement: ContDiff Complex n fun x => Complex.sinh (f x)
  proof: Complex.contDiff_sinh.comp h

中文:
定理 连续可微.csinh
  条件: {n} (h : 连续可微 复形 n f)
  结论: 连续可微 复形 n fun x => 复形.sinh (f x)
  证明: Complex.contDiff_sinh.comp h

Depends on / 依赖: Complex.contDiff_sinh.comp, contDiff_sinh
-/
theorem ContDiff.csinh {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x => Complex.sinh (f x) :=
  Complex.contDiff_sinh.comp h

/--
theorem `ContDiffAt.csinh` / 定理 `ContDiffAt.csinh`

English:
theorem ContDiffAt.csinh
  given: {n} (hf : ContDiffAt Complex n f x)
  proof: Complex.contDiff_sinh.contDiffAt.comp x hf

中文:
定理 ContDiffAt.csinh
  条件: {n} (hf : ContDiffAt 复形 n f x)
  证明: Complex.contDiff_sinh.contDiffAt.comp x hf

Depends on / 依赖: Complex.contDiff_sinh.contDiffAt.comp, contDiffAt, contDiff_sinh
-/
theorem ContDiffAt.csinh {n} (hf : ContDiffAt Complex n f x) :
    ContDiffAt Complex n (fun x => Complex.sinh (f x)) x :=
  Complex.contDiff_sinh.contDiffAt.comp x hf

/--
theorem `ContDiffOn.csinh` / 定理 `ContDiffOn.csinh`

English:
theorem ContDiffOn.csinh
  given: {n} (hf : ContDiffOn Complex n f s)
  proof: Complex.contDiff_sinh.comp_contDiffOn hf

中文:
定理 ContDiffOn.csinh
  条件: {n} (hf : ContDiffOn 复形 n f s)
  证明: Complex.contDiff_sinh.comp_contDiffOn hf

Depends on / 依赖: Complex.contDiff_sinh.comp_contDiffOn, comp_contDiffOn, contDiff_sinh
-/
theorem ContDiffOn.csinh {n} (hf : ContDiffOn Complex n f s) :
    ContDiffOn Complex n (fun x => Complex.sinh (f x)) s :=
  Complex.contDiff_sinh.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.csinh` / 定理 `ContDiffWithinAt.csinh`

English:
theorem ContDiffWithinAt.csinh
  given: {n} (hf : ContDiffWithinAt Complex n f s x)
  proof: Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.csinh
  条件: {n} (hf : ContDiffWithinAt 复形 n f s x)
  证明: Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_sinh
-/
theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt Complex n f s x) :
    ContDiffWithinAt Complex n (fun x => Complex.sinh (f x)) s x :=
  Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y z : Real}

/--
theorem `hasStrictDerivAt_sinh` / 定理 `hasStrictDerivAt_sinh`

English:
theorem hasStrictDerivAt_sinh
  given: (x : Real)
  statement: HasStrictDerivAt sinh (cosh x) x
  proof: (Complex.hasStrictDerivAt_sinh x).real_of_complex

中文:
定理 hasStrictDerivAt_sinh
  条件: (x : 实数)
  结论: HasStrictDerivAt sinh (cosh x) x
  证明: (Complex.hasStrictDerivAt_sinh x).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_sinh, hasStrictDerivAt_sinh, real_of_complex
-/
theorem hasStrictDerivAt_sinh (x : Real) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex

/--
theorem `hasDerivAt_sinh` / 定理 `hasDerivAt_sinh`

English:
theorem hasDerivAt_sinh
  given: (x : Real)
  statement: HasDerivAt sinh (cosh x) x
  proof: (Complex.hasDerivAt_sinh x).real_of_complex

中文:
定理 hasDerivAt_sinh
  条件: (x : 实数)
  结论: 在点处可导 sinh (cosh x) x
  证明: (Complex.hasDerivAt_sinh x).real_of_complex

Depends on / 依赖: Complex.hasDerivAt_sinh, EffectiveEpi, hasDerivAt_sinh, real_of_complex, strongEpi_of_effectiveEpi
-/
theorem hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex

/--
theorem `isEquivalent_sinh` / 定理 `isEquivalent_sinh`

English:
theorem isEquivalent_sinh
  statement: sinh ~[𝓝 0] id
  proof: by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]

中文:
定理 isEquivalent_sinh
  结论: sinh ~[𝓝 0] id
  证明: by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]

Depends on / 依赖: hasDerivAt_sinh, isLittleO
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
/--
theorem `contDiff_sinh` / 定理 `contDiff_sinh`

English:
theorem contDiff_sinh
  given: {n}
  statement: ContDiff Real n sinh
  proof: Complex.contDiff_sinh.real_of_complex

@[simp]

中文:
定理 contDiff_sinh
  条件: {n}
  结论: 连续可微 实数 n sinh
  证明: Complex.contDiff_sinh.real_of_complex

@[simp]

Depends on / 依赖: Complex.contDiff_sinh.real_of_complex, contDiff_sinh, real_of_complex
-/
theorem contDiff_sinh {n} : ContDiff Real n sinh :=
  Complex.contDiff_sinh.real_of_complex

@[simp]
/--
theorem `differentiable_sinh` / 定理 `differentiable_sinh`

English:
theorem differentiable_sinh
  statement: Differentiable Real sinh
  proof: fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]

中文:
定理 differentiable_sinh
  结论: 可微 实数 sinh
  证明: fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_sinh
-/
theorem differentiable_sinh : Differentiable Real sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
/--
theorem `differentiableAt_sinh` / 定理 `differentiableAt_sinh`

English:
theorem differentiableAt_sinh
  statement: DifferentiableAt Real sinh x
  proof: differentiable_sinh x

中文:
定理 differentiableAt_sinh
  结论: DifferentiableAt 实数 sinh x
  证明: differentiable_sinh x

Depends on / 依赖: differentiable_sinh
-/
theorem differentiableAt_sinh : DifferentiableAt Real sinh x :=
  differentiable_sinh x

/-- The function `Real.sinh` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_sinh` / 引理 `analyticAt_sinh`

English:
lemma analyticAt_sinh
  statement: AnalyticAt Real sinh x
  proof: contDiff_sinh.contDiffAt.analyticAt

中文:
引理 analyticAt_sinh
  结论: AnalyticAt 实数 sinh x
  证明: contDiff_sinh.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_sinh, contDiff_sinh.contDiffAt.analyticAt
-/
lemma analyticAt_sinh : AnalyticAt Real sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_sinh` / 引理 `analyticWithinAt_sinh`

English:
lemma analyticWithinAt_sinh
  given: {s : Set Real}
  statement: AnalyticWithinAt Real sinh s x
  proof: contDiff_sinh.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_sinh
  条件: {s : 集合 实数}
  结论: AnalyticWithinAt 实数 sinh s x
  证明: contDiff_sinh.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_sinh, contDiff_sinh.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_sinh {s : Set Real} : AnalyticWithinAt Real sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_sinh` / 定理 `analyticOnNhd_sinh`

English:
theorem analyticOnNhd_sinh
  given: {s : Set Real}
  statement: AnalyticOnNhd Real sinh s
  proof: fun _ _ => analyticAt_sinh

中文:
定理 analyticOnNhd_sinh
  条件: {s : 集合 实数}
  结论: AnalyticOnNhd 实数 sinh s
  证明: fun _ _ => analyticAt_sinh

Depends on / 依赖: analyticAt_sinh, effectiveEpiFamilyStructSingletonOfEffectiveEpi
-/
theorem analyticOnNhd_sinh {s : Set Real} : AnalyticOnNhd Real sinh s :=
  fun _ _ => analyticAt_sinh

/--
lemma `analyticOn_sinh` / 引理 `analyticOn_sinh`

English:
lemma analyticOn_sinh
  given: {s : Set Real}
  statement: AnalyticOn Real sinh s
  proof: contDiff_sinh.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_sinh
  条件: {s : 集合 实数}
  结论: AnalyticOn 实数 sinh s
  证明: contDiff_sinh.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_sinh, contDiff_sinh.contDiffOn.analyticOn
-/
lemma analyticOn_sinh {s : Set Real} : AnalyticOn Real sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_sinh` / 定理 `deriv_sinh`

English:
theorem deriv_sinh
  statement: deriv sinh = cosh
  proof: funext fun x => (hasDerivAt_sinh x).deriv

中文:
定理 deriv_sinh
  结论: deriv sinh = cosh
  证明: funext fun x => (hasDerivAt_sinh x).deriv

Depends on / 依赖: effectiveEpiStructOfEffectiveEpiFamilySingleton, hasDerivAt_sinh
-/
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/--
theorem `hasStrictDerivAt_cosh` / 定理 `hasStrictDerivAt_cosh`

English:
theorem hasStrictDerivAt_cosh
  given: (x : Real)
  statement: HasStrictDerivAt cosh (sinh x) x
  proof: (Complex.hasStrictDerivAt_cosh x).real_of_complex

中文:
定理 hasStrictDerivAt_cosh
  条件: (x : 实数)
  结论: HasStrictDerivAt cosh (sinh x) x
  证明: (Complex.hasStrictDerivAt_cosh x).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_cosh, hasStrictDerivAt_cosh, real_of_complex
-/
theorem hasStrictDerivAt_cosh (x : Real) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.hasStrictDerivAt_cosh x).real_of_complex

/--
theorem `hasDerivAt_cosh` / 定理 `hasDerivAt_cosh`

English:
theorem hasDerivAt_cosh
  given: (x : Real)
  statement: HasDerivAt cosh (sinh x) x
  proof: (Complex.hasDerivAt_cosh x).real_of_complex

@[fun_prop]

中文:
定理 hasDerivAt_cosh
  条件: (x : 实数)
  结论: 在点处可导 cosh (sinh x) x
  证明: (Complex.hasDerivAt_cosh x).real_of_complex

@[fun_prop]

Depends on / 依赖: Complex.hasDerivAt_cosh, hasDerivAt_cosh, real_of_complex
-/
theorem hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex

@[fun_prop]
/--
theorem `contDiff_cosh` / 定理 `contDiff_cosh`

English:
theorem contDiff_cosh
  given: {n}
  statement: ContDiff Real n cosh
  proof: Complex.contDiff_cosh.real_of_complex

@[simp]

中文:
定理 contDiff_cosh
  条件: {n}
  结论: 连续可微 实数 n cosh
  证明: Complex.contDiff_cosh.real_of_complex

@[simp]

Depends on / 依赖: Complex.contDiff_cosh.real_of_complex, contDiff_cosh, effectiveEpiFamilyStructOfIsIsoDesc, real_of_complex
-/
theorem contDiff_cosh {n} : ContDiff Real n cosh :=
  Complex.contDiff_cosh.real_of_complex

@[simp]
/--
theorem `differentiable_cosh` / 定理 `differentiable_cosh`

English:
theorem differentiable_cosh
  statement: Differentiable Real cosh
  proof: fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]

中文:
定理 differentiable_cosh
  结论: 可微 实数 cosh
  证明: fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_cosh
-/
theorem differentiable_cosh : Differentiable Real cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
/--
theorem `differentiableAt_cosh` / 定理 `differentiableAt_cosh`

English:
theorem differentiableAt_cosh
  statement: DifferentiableAt Real cosh x
  proof: differentiable_cosh x

中文:
定理 differentiableAt_cosh
  结论: DifferentiableAt 实数 cosh x
  证明: differentiable_cosh x

Depends on / 依赖: differentiable_cosh, effectiveEpiStructOfIsIso
-/
theorem differentiableAt_cosh : DifferentiableAt Real cosh x :=
  differentiable_cosh x

/-- The function `Real.cosh` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_cosh` / 引理 `analyticAt_cosh`

English:
lemma analyticAt_cosh
  statement: AnalyticAt Real cosh x
  proof: contDiff_cosh.contDiffAt.analyticAt

中文:
引理 analyticAt_cosh
  结论: AnalyticAt 实数 cosh x
  证明: contDiff_cosh.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_cosh, contDiff_cosh.contDiffAt.analyticAt
-/
lemma analyticAt_cosh : AnalyticAt Real cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_cosh` / 引理 `analyticWithinAt_cosh`

English:
lemma analyticWithinAt_cosh
  given: {s : Set Real}
  statement: AnalyticWithinAt Real cosh s x
  proof: contDiff_cosh.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_cosh
  条件: {s : 集合 实数}
  结论: AnalyticWithinAt 实数 cosh s x
  证明: contDiff_cosh.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_cosh, contDiff_cosh.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_cosh {s : Set Real} : AnalyticWithinAt Real cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_cosh` / 定理 `analyticOnNhd_cosh`

English:
theorem analyticOnNhd_cosh
  given: {s : Set Real}
  statement: AnalyticOnNhd Real cosh s
  proof: fun _ _ => analyticAt_cosh

中文:
定理 analyticOnNhd_cosh
  条件: {s : 集合 实数}
  结论: AnalyticOnNhd 实数 cosh s
  证明: fun _ _ => analyticAt_cosh

Depends on / 依赖: analyticAt_cosh
-/
theorem analyticOnNhd_cosh {s : Set Real} : AnalyticOnNhd Real cosh s :=
  fun _ _ => analyticAt_cosh

/--
lemma `analyticOn_cosh` / 引理 `analyticOn_cosh`

English:
lemma analyticOn_cosh
  given: {s : Set Real}
  statement: AnalyticOn Real cosh s
  proof: contDiff_cosh.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_cosh
  条件: {s : 集合 实数}
  结论: AnalyticOn 实数 cosh s
  证明: contDiff_cosh.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_cosh, contDiff_cosh.contDiffOn.analyticOn
-/
lemma analyticOn_cosh {s : Set Real} : AnalyticOn Real cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_cosh` / 定理 `deriv_cosh`

English:
theorem deriv_cosh
  statement: deriv cosh = sinh
  proof: funext fun x => (hasDerivAt_cosh x).deriv

中文:
定理 deriv_cosh
  结论: deriv cosh = sinh
  证明: funext fun x => (hasDerivAt_cosh x).deriv

Depends on / 依赖: effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi, hasDerivAt_cosh
-/
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

/--
theorem `sinh_strictMono` / 定理 `sinh_strictMono`

English:
theorem sinh_strictMono
  statement: StrictMono sinh
  proof: strictMono_of_deriv_pos by rw [Real.deriv_sinh]; exact cosh_pos

中文:
定理 sinh_strictMono
  结论: 严格递增 sinh
  证明: strictMono_of_deriv_pos by rw [Real.deriv_sinh]; exact cosh_pos

Depends on / 依赖: Real.deriv_sinh, cosh_pos, deriv_sinh, strictMono_of_deriv_pos
-/
theorem sinh_strictMono : StrictMono sinh :=
strictMono_of_deriv_pos by rw [Real.deriv_sinh]; exact cosh_pos

/--
theorem `sinh_injective` / 定理 `sinh_injective`

English:
theorem sinh_injective
  statement: Function.Injective sinh
  proof: sinh_strictMono.injective

@[simp]

中文:
定理 sinh_injective
  结论: 函数.单射 sinh
  证明: sinh_strictMono.injective

@[simp]

Depends on / 依赖: injective, sinh_strictMono, sinh_strictMono.injective
-/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strictMono.injective

@[simp]
/--
theorem `sinh_inj` / 定理 `sinh_inj`

English:
theorem sinh_inj
  statement: sinh x = sinh y ↔ x = y
  proof: sinh_injective.eq_iff

@[simp]

中文:
定理 sinh_inj
  结论: sinh x = sinh y ↔ x = y
  证明: sinh_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, sinh_injective, sinh_injective.eq_iff
-/
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff

@[simp]
/--
theorem `sinh_le_sinh` / 定理 `sinh_le_sinh`

English:
theorem sinh_le_sinh
  statement: sinh x <= sinh y ↔ x <= y
  proof: sinh_strictMono.le_iff_le

@[simp]

中文:
定理 sinh_le_sinh
  结论: sinh x <= sinh y ↔ x <= y
  证明: sinh_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, sinh_strictMono, sinh_strictMono.le_iff_le
-/
theorem sinh_le_sinh : sinh x <= sinh y ↔ x <= y :=
  sinh_strictMono.le_iff_le

@[simp]
/--
theorem `sinh_lt_sinh` / 定理 `sinh_lt_sinh`

English:
theorem sinh_lt_sinh
  statement: sinh x < sinh y ↔ x < y
  proof: sinh_strictMono.lt_iff_lt

中文:
定理 sinh_lt_sinh
  结论: sinh x < sinh y ↔ x < y
  证明: sinh_strictMono.lt_iff_lt

Depends on / 依赖: lt_iff_lt, sinh_strictMono, sinh_strictMono.lt_iff_lt
-/
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strictMono.lt_iff_lt

/--
lemma `sinh_eq_zero` / 引理 `sinh_eq_zero`

English:
lemma sinh_eq_zero
  statement: sinh x = 0 ↔ x = 0
  proof: by rw [← @sinh_inj x, sinh_zero]

中文:
引理 sinh_eq_zero
  结论: sinh x = 0 ↔ x = 0
  证明: by rw [← @sinh_inj x, sinh_zero]
-/
@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]

/--
lemma `sinh_ne_zero` / 引理 `sinh_ne_zero`

English:
lemma sinh_ne_zero
  statement: sinh x != 0 ↔ x != 0
  proof: sinh_eq_zero.not

@[simp]

中文:
引理 sinh_ne_zero
  结论: sinh x != 0 ↔ x != 0
  证明: sinh_eq_zero.not

@[simp]

Depends on / 依赖: sinh_eq_zero, sinh_eq_zero.not
-/
lemma sinh_ne_zero : sinh x != 0 ↔ x != 0 := sinh_eq_zero.not

@[simp]
/--
theorem `sinh_pos_iff` / 定理 `sinh_pos_iff`

English:
theorem sinh_pos_iff
  statement: 0 < sinh x ↔ 0 < x
  proof: by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

@[simp]

中文:
定理 sinh_pos_iff
  结论: 0 < sinh x ↔ 0 < x
  证明: by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

@[simp]

Depends on / 依赖: sinh_lt_sinh, sinh_zero
-/
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

@[simp]
/--
theorem `sinh_nonpos_iff` / 定理 `sinh_nonpos_iff`

English:
theorem sinh_nonpos_iff
  statement: sinh x <= 0 ↔ x <= 0
  proof: by simpa only [sinh_zero] using @sinh_le_sinh x 0

@[simp]

中文:
定理 sinh_nonpos_iff
  结论: sinh x <= 0 ↔ x <= 0
  证明: by simpa only [sinh_zero] using @sinh_le_sinh x 0

@[simp]

Depends on / 依赖: Category, Category.id_comp, Cocone, Cocone.ext_inv_hom, Cofan.mk_pt, IsColimit, IsColimit.ofIsoColimit_desc, Iso.refl_inv, cocone_x, colimit, colimit.cocone_x, colimit.isColimit_desc, coproductIsCoproduct, effectiveEpiStructIsColimitDescOfEffectiveEpiFamily, ext_inv_hom, id_comp, isColimit_desc, mk_pt, ofIsoColimit_desc, refl_inv
-/
theorem sinh_nonpos_iff : sinh x <= 0 ↔ x <= 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0

@[simp]
/--
theorem `sinh_neg_iff` / 定理 `sinh_neg_iff`

English:
theorem sinh_neg_iff
  statement: sinh x < 0 ↔ x < 0
  proof: by simpa only [sinh_zero] using @sinh_lt_sinh x 0

@[simp]

中文:
定理 sinh_neg_iff
  结论: sinh x < 0 ↔ x < 0
  证明: by simpa only [sinh_zero] using @sinh_lt_sinh x 0

@[simp]

Depends on / 依赖: sinh_lt_sinh, sinh_zero
-/
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0

@[simp]
/--
theorem `sinh_nonneg_iff` / 定理 `sinh_nonneg_iff`

English:
theorem sinh_nonneg_iff
  statement: 0 <= sinh x ↔ 0 <= x
  proof: by simpa only [sinh_zero] using @sinh_le_sinh 0 x

中文:
定理 sinh_nonneg_iff
  结论: 0 <= sinh x ↔ 0 <= x
  证明: by simpa only [sinh_zero] using @sinh_le_sinh 0 x

Depends on / 依赖: sinh_le_sinh, sinh_zero
-/
theorem sinh_nonneg_iff : 0 <= sinh x ↔ 0 <= x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x

/--
theorem `abs_sinh` / 定理 `abs_sinh`

English:
theorem abs_sinh
  given: (x : Real)
  statement: |sinh x| = sinh |x|
  proof: by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

中文:
定理 abs_sinh
  条件: (x : 实数)
  结论: |sinh x| = sinh |x|
  证明: by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_total
-/
theorem abs_sinh (x : Real) : |sinh x| = sinh |x| := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

/--
theorem `cosh_strictMonoOn` / 定理 `cosh_strictMonoOn`

English:
theorem cosh_strictMonoOn
  statement: StrictMonoOn cosh (Ici 0)
  proof: strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici]; rw [mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

@[simp]

中文:
定理 cosh_strictMonoOn
  结论: StrictMonoOn cosh (左闭右无界区间 0)
  证明: strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici]; rw [mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

@[simp]

Depends on / 依赖: continuousOn, continuous_cosh, continuous_cosh.continuousOn, convex_Ici, deriv_cosh, interior_Ici, mem_Ioi, sinh_pos_iff, strictMonoOn_of_deriv_pos
-/
theorem cosh_strictMonoOn : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici]; rw [mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

@[simp]
/--
theorem `cosh_le_cosh` / 定理 `cosh_le_cosh`

English:
theorem cosh_le_cosh
  statement: cosh x <= cosh y ↔ |x| <= |y|
  proof: cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]

中文:
定理 cosh_le_cosh
  结论: cosh x <= cosh y ↔ |x| <= |y|
  证明: cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]

Depends on / 依赖: EffectivelyEnough, EffectivelyEnough.presentation, abs_nonneg, cosh_abs, cosh_strictMonoOn, cosh_strictMonoOn.le_iff_le, effectiveEpi, le_iff_le, presentation, some.effectiveEpi
-/
theorem cosh_le_cosh : cosh x <= cosh y ↔ |x| <= |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]
/--
theorem `cosh_lt_cosh` / 定理 `cosh_lt_cosh`

English:
theorem cosh_lt_cosh
  statement: cosh x < cosh y ↔ |x| < |y|
  proof: lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]

中文:
定理 cosh_lt_cosh
  结论: cosh x < cosh y ↔ |x| < |y|
  证明: lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]

Depends on / 依赖: cosh_le_cosh, lt_iff_lt_of_le_iff_le
-/
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]
/--
theorem `one_le_cosh` / 定理 `one_le_cosh`

English:
theorem one_le_cosh
  given: (x : Real)
  statement: 1 <= cosh x
  proof: cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

@[simp]

中文:
定理 one_le_cosh
  条件: (x : 实数)
  结论: 1 <= cosh x
  证明: cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

@[simp]

Depends on / 依赖: _root_, _root_.abs_nonneg, _root_.abs_zero, abs_nonneg, abs_zero, cosh_le_cosh, cosh_zero
-/
theorem one_le_cosh (x : Real) : 1 <= cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

@[simp]
/--
theorem `one_lt_cosh` / 定理 `one_lt_cosh`

English:
theorem one_lt_cosh
  statement: 1 < cosh x ↔ x != 0
  proof: cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])

中文:
定理 one_lt_cosh
  结论: 1 < cosh x ↔ x != 0
  证明: cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])

Depends on / 依赖: _root_, _root_.abs_zero, abs_pos, abs_zero, cosh_lt_cosh, cosh_lt_cosh.trans, cosh_zero
-/
theorem one_lt_cosh : 1 < cosh x ↔ x != 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])

/--
theorem `sinh_sub_id_strictMono` / 定理 `sinh_sub_id_strictMono`

English:
theorem sinh_sub_id_strictMono
  statement: StrictMono fun x => sinh x - x
  proof: by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub]; rw [deriv_sinh]; rw [deriv_id'']; 

中文:
定理 sinh_sub_id_strictMono
  结论: 严格递增 fun x => sinh x - x
  证明: by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub]; rw [deriv_sinh]; rw [deriv_id'']; 

Depends on / 依赖: continuousOn, continuous_id, continuous_sinh, continuous_sinh.sub, convex_Ici, deriv_fun_sub, deriv_id, deriv_sinh, differentiableAt_id, differentiableAt_sinh, exacts, hx.ne, interior_Ici, mem_Ioi, one_lt_cosh, strictMonoOn_of_deriv_pos, strictMono_of_odd_strictMonoOn_nonneg, sub_pos
-/
theorem sinh_sub_id_strictMono : StrictMono fun x => sinh x - x := by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub]; rw [deriv_sinh]; rw [deriv_id'']; rw [sub_pos]; rw [one_lt_cosh]
    exacts [hx.ne', differentiableAt_sinh, differentiableAt_id]

@[simp]
/--
theorem `self_le_sinh_iff` / 定理 `self_le_sinh_iff`

English:
theorem self_le_sinh_iff
  statement: x <= sinh x ↔ 0 <= x
  proof: calc
    x <= sinh x ↔ sinh 0 - 0 <= sinh x - x := by simp
    _ ↔ 0 <= x := sinh_sub_id_strictMono.le_iff_le

@[simp]

中文:
定理 self_le_sinh_iff
  结论: x <= sinh x ↔ 0 <= x
  证明: calc
    x <= sinh x ↔ sinh 0 - 0 <= sinh x - x := by simp
    _ ↔ 0 <= x := sinh_sub_id_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, sinh_sub_id_strictMono, sinh_sub_id_strictMono.le_iff_le
-/
theorem self_le_sinh_iff : x <= sinh x ↔ 0 <= x :=
  calc
    x <= sinh x ↔ sinh 0 - 0 <= sinh x - x := by simp
    _ ↔ 0 <= x := sinh_sub_id_strictMono.le_iff_le

@[simp]
/--
theorem `sinh_le_self_iff` / 定理 `sinh_le_self_iff`

English:
theorem sinh_le_self_iff
  statement: sinh x <= x ↔ x <= 0
  proof: calc
    sinh x <= x ↔ sinh x - x <= sinh 0 - 0 := by simp
    _ ↔ x <= 0 := sinh_sub_id_strictMono.le_iff_le

@[simp]

中文:
定理 sinh_le_self_iff
  结论: sinh x <= x ↔ x <= 0
  证明: calc
    sinh x <= x ↔ sinh x - x <= sinh 0 - 0 := by simp
    _ ↔ x <= 0 := sinh_sub_id_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, sinh_sub_id_strictMono, sinh_sub_id_strictMono.le_iff_le
-/
theorem sinh_le_self_iff : sinh x <= x ↔ x <= 0 :=
  calc
    sinh x <= x ↔ sinh x - x <= sinh 0 - 0 := by simp
    _ ↔ x <= 0 := sinh_sub_id_strictMono.le_iff_le

@[simp]
/--
theorem `self_lt_sinh_iff` / 定理 `self_lt_sinh_iff`

English:
theorem self_lt_sinh_iff
  statement: x < sinh x ↔ 0 < x
  proof: lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]

中文:
定理 self_lt_sinh_iff
  结论: x < sinh x ↔ 0 < x
  证明: lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, sinh_le_self_iff
-/
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]
/--
theorem `sinh_lt_self_iff` / 定理 `sinh_lt_self_iff`

English:
theorem sinh_lt_self_iff
  statement: sinh x < x ↔ x < 0
  proof: lt_iff_lt_of_le_iff_le self_le_sinh_iff

中文:
定理 sinh_lt_self_iff
  结论: sinh x < x ↔ x < 0
  证明: lt_iff_lt_of_le_iff_le self_le_sinh_iff

Depends on / 依赖: F.asEquivalence, asEquivalence, effectiveEpiFamilyStructOfEquivalence, lt_iff_lt_of_le_iff_le, self_le_sinh_iff
-/
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sinh` and `cosh`. -/

namespace Complex

@[simp]
/--
theorem `iteratedDeriv_add_one_sinh` / 定理 `iteratedDeriv_add_one_sinh`

English:
theorem iteratedDeriv_add_one_sinh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_sinh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_sinh (n : Nat) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_add_one_cosh` / 定理 `iteratedDeriv_add_one_cosh`

English:
theorem iteratedDeriv_add_one_cosh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_cosh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_cosh (n : Nat) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_even_sinh` / 定理 `iteratedDeriv_even_sinh`

English:
theorem iteratedDeriv_even_sinh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]

中文:
定理 iteratedDeriv_even_sinh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]

Depends on / 依赖: mul_add
-/
theorem iteratedDeriv_even_sinh (n : Nat) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
/--
theorem `iteratedDeriv_even_cosh` / 定理 `iteratedDeriv_even_cosh`

English:
theorem iteratedDeriv_even_cosh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

中文:
定理 iteratedDeriv_even_cosh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

Depends on / 依赖: mul_add
-/
theorem iteratedDeriv_even_cosh (n : Nat) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
theorem `iteratedDeriv_odd_sinh` / 定理 `iteratedDeriv_odd_sinh`

English:
theorem iteratedDeriv_odd_sinh
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_sinh
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_sinh (n : Nat) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

/--
theorem `iteratedDeriv_odd_cosh` / 定理 `iteratedDeriv_odd_cosh`

English:
theorem iteratedDeriv_odd_cosh
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_cosh
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_cosh (n : Nat) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

/--
theorem `differentiable_iteratedDeriv_sinh` / 定理 `differentiable_iteratedDeriv_sinh`

English:
theorem differentiable_iteratedDeriv_sinh
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

中文:
定理 differentiable_iteratedDeriv_sinh
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

Depends on / 依赖: differentiable_iteratedDeriv_sinh
-/
theorem differentiable_iteratedDeriv_sinh (n : Nat) :
    Differentiable Complex (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

/--
theorem `differentiable_iteratedDeriv_cosh` / 定理 `differentiable_iteratedDeriv_cosh`

English:
theorem differentiable_iteratedDeriv_cosh
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

中文:
定理 differentiable_iteratedDeriv_cosh
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

Depends on / 依赖: differentiable_iteratedDeriv_cosh
-/
theorem differentiable_iteratedDeriv_cosh (n : Nat) :
    Differentiable Complex (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

end Complex

namespace Real

@[simp]
/--
theorem `iteratedDeriv_add_one_sinh` / 定理 `iteratedDeriv_add_one_sinh`

English:
theorem iteratedDeriv_add_one_sinh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_sinh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: infer_instance, iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_sinh (n : Nat) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_add_one_cosh` / 定理 `iteratedDeriv_add_one_cosh`

English:
theorem iteratedDeriv_add_one_cosh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_cosh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: infer_instance, iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_cosh (n : Nat) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_even_sinh` / 定理 `iteratedDeriv_even_sinh`

English:
theorem iteratedDeriv_even_sinh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]

中文:
定理 iteratedDeriv_even_sinh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]

Depends on / 依赖: infer_instance, mul_add
-/
theorem iteratedDeriv_even_sinh (n : Nat) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
/--
theorem `iteratedDeriv_even_cosh` / 定理 `iteratedDeriv_even_cosh`

English:
theorem iteratedDeriv_even_cosh
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

中文:
定理 iteratedDeriv_even_cosh
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

Depends on / 依赖: mul_add
-/
theorem iteratedDeriv_even_cosh (n : Nat) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
theorem `iteratedDeriv_odd_sinh` / 定理 `iteratedDeriv_odd_sinh`

English:
theorem iteratedDeriv_odd_sinh
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_sinh
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_sinh (n : Nat) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

/--
theorem `iteratedDeriv_odd_cosh` / 定理 `iteratedDeriv_odd_cosh`

English:
theorem iteratedDeriv_odd_cosh
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_cosh
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_cosh (n : Nat) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

/--
theorem `differentiable_iteratedDeriv_sinh` / 定理 `differentiable_iteratedDeriv_sinh`

English:
theorem differentiable_iteratedDeriv_sinh
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

中文:
定理 differentiable_iteratedDeriv_sinh
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

Depends on / 依赖: F.effectiveEpiFamily_of_map, differentiable_iteratedDeriv_sinh, effectiveEpiFamily_of_map, infer_instance
-/
theorem differentiable_iteratedDeriv_sinh (n : Nat) :
    Differentiable Real (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

/--
theorem `differentiable_iteratedDeriv_cosh` / 定理 `differentiable_iteratedDeriv_cosh`

English:
theorem differentiable_iteratedDeriv_cosh
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

@[simp]

中文:
定理 differentiable_iteratedDeriv_cosh
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

@[simp]

Depends on / 依赖: F.finite_effectiveEpiFamily_of_map, differentiable_iteratedDeriv_cosh, effectiveEpi_iff_effectiveEpiFamily, finite_effectiveEpiFamily_of_map, infer_instance
-/
theorem differentiable_iteratedDeriv_cosh (n : Nat) :
    Differentiable Real (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

@[simp]
/--
theorem `iteratedDerivWithin_sinh_Icc` / 定理 `iteratedDerivWithin_sinh_Icc`

English:
theorem iteratedDerivWithin_sinh_Icc
  given: (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_sinh_Icc
  条件: (n : 自然数) {a b : 实数} (h : a < b) {x : 实数} (hx : x in 闭区间 a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

@[simp]

Depends on / 依赖: EffectiveEpiFamily, F.map, F.obj, Iso.hom_inv_id_app_assoc, asEquivalence, contDiffAt, contDiff_sinh, contDiff_sinh.contDiffAt, hom_inv_id_app_assoc, inv_fun_map, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Icc, unit.app, unitInv, unitInv.app
-/
theorem iteratedDerivWithin_sinh_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b) :
    iteratedDerivWithin n sinh (Icc a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_cosh_Icc` / 定理 `iteratedDerivWithin_cosh_Icc`

English:
theorem iteratedDerivWithin_cosh_Icc
  given: (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_cosh_Icc
  条件: (n : 自然数) {a b : 实数} (h : a < b) {x : 实数} (hx : x in 闭区间 a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

@[simp]

Depends on / 依赖: F.effectiveEpi_of_map, G.effectiveEpi_of_map, contDiffAt, contDiff_cosh, contDiff_cosh.contDiffAt, effectiveEpi_of_map, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Icc
-/
theorem iteratedDerivWithin_cosh_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b) :
    iteratedDerivWithin n cosh (Icc a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_sinh_Ioo` / 定理 `iteratedDerivWithin_sinh_Ioo`

English:
theorem iteratedDerivWithin_sinh_Ioo
  given: (n : Nat) {a b x : Real} (hx : x in Ioo a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_sinh_Ioo
  条件: (n : 自然数) {a b x : 实数} (hx : x in 开区间 a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

@[simp]

Depends on / 依赖: F.finite_effectiveEpiFamily_of_map, G.finite_effectiveEpiFamily_of_map, contDiffAt, contDiff_sinh, contDiff_sinh.contDiffAt, finite_effectiveEpiFamily_of_map, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Ioo
-/
theorem iteratedDerivWithin_sinh_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
    iteratedDerivWithin n sinh (Ioo a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_cosh_Ioo` / 定理 `iteratedDerivWithin_cosh_Ioo`

English:
theorem iteratedDerivWithin_cosh_Ioo
  given: (n : Nat) {a b x : Real} (hx : x in Ioo a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

中文:
定理 iteratedDerivWithin_cosh_Ioo
  条件: (n : 自然数) {a b x : 实数} (hx : x in 开区间 a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

Depends on / 依赖: F.effectiveEpiFamily_of_map, G.effectiveEpiFamily_of_map, contDiffAt, contDiff_cosh, contDiff_cosh.contDiffAt, effectiveEpiFamily_of_map, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Ioo
-/
theorem iteratedDerivWithin_cosh_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
    iteratedDerivWithin n cosh (Ioo a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/

variable {f : Real -> Real} {f' x : Real} {s : Set Real}


/--
theorem `HasStrictDerivAt.cosh` / 定理 `HasStrictDerivAt.cosh`

English:
theorem HasStrictDerivAt.cosh
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_cosh (f x)).comp x hf

中文:
定理 HasStrictDerivAt.cosh
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_cosh (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_cosh, hasStrictDerivAt_cosh
-/
theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp x hf

/--
theorem `HasDerivAt.cosh` / 定理 `HasDerivAt.cosh`

English:
theorem HasDerivAt.cosh
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_cosh (f x)).comp x hf

中文:
定理 在点处可导.cosh
  条件: (hf : 在点处可导 f f' x)
  证明: (Real.hasDerivAt_cosh (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_cosh, hasDerivAt_cosh
-/
theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasDerivAt_cosh (f x)).comp x hf

/--
theorem `HasDerivWithinAt.cosh` / 定理 `HasDerivWithinAt.cosh`

English:
theorem HasDerivWithinAt.cosh
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.cosh
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_cosh, comp_hasDerivWithinAt, hasDerivAt_cosh
-/
theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_cosh` / 定理 `derivWithin_cosh`

English:
theorem derivWithin_cosh
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.cosh.derivWithin hxs

@[simp]

中文:
定理 derivWithin_cosh
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.cosh.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.cosh.derivWithin
-/
theorem derivWithin_cosh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cosh.derivWithin hxs

@[simp]
/--
theorem `deriv_cosh` / 定理 `deriv_cosh`

English:
theorem deriv_cosh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.cosh.deriv

中文:
定理 deriv_cosh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.cosh.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.cosh.deriv
-/
theorem deriv_cosh (hc : DifferentiableAt Real f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.hasDerivAt.cosh.deriv


/--
theorem `HasStrictDerivAt.sinh` / 定理 `HasStrictDerivAt.sinh`

English:
theorem HasStrictDerivAt.sinh
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_sinh (f x)).comp x hf

中文:
定理 HasStrictDerivAt.sinh
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_sinh (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_sinh, hasStrictDerivAt_sinh
-/
theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp x hf

/--
theorem `HasDerivAt.sinh` / 定理 `HasDerivAt.sinh`

English:
theorem HasDerivAt.sinh
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_sinh (f x)).comp x hf

中文:
定理 在点处可导.sinh
  条件: (hf : 在点处可导 f f' x)
  证明: (Real.hasDerivAt_sinh (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_sinh, hasDerivAt_sinh
-/
theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasDerivAt_sinh (f x)).comp x hf

/--
theorem `HasDerivWithinAt.sinh` / 定理 `HasDerivWithinAt.sinh`

English:
theorem HasDerivWithinAt.sinh
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.sinh
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_sinh, comp_hasDerivWithinAt, hasDerivAt_sinh
-/
theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_sinh` / 定理 `derivWithin_sinh`

English:
theorem derivWithin_sinh
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.sinh.derivWithin hxs

@[simp]

中文:
定理 derivWithin_sinh
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.sinh.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.sinh.derivWithin
-/
theorem derivWithin_sinh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sinh.derivWithin hxs

@[simp]
/--
theorem `deriv_sinh` / 定理 `deriv_sinh`

English:
theorem deriv_sinh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.sinh.deriv

中文:
定理 deriv_sinh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.sinh.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.sinh.deriv
-/
theorem deriv_sinh (hc : DifferentiableAt Real f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.hasDerivAt.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {f' : StrongDual Real E}
  {x : E} {s : Set E}


/--
theorem `HasStrictFDerivAt.cosh` / 定理 `HasStrictFDerivAt.cosh`

English:
theorem HasStrictFDerivAt.cosh
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.cosh
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Real.hasStrictDerivAt_cosh, comp_hasStrictFDerivAt, hasStrictDerivAt_cosh
-/
theorem HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.cosh` / 定理 `HasFDerivAt.cosh`

English:
theorem HasFDerivAt.cosh
  given: (hf : HasFDerivAt f f' x)
  proof: (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.cosh
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Real.hasDerivAt_cosh, comp_hasFDerivAt, hasDerivAt_cosh
-/
theorem HasFDerivAt.cosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.cosh` / 定理 `HasFDerivWithinAt.cosh`

English:
theorem HasFDerivWithinAt.cosh
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.cosh
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_cosh, comp_hasFDerivWithinAt, hasDerivAt_cosh
-/
theorem HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.cosh` / 定理 `DifferentiableWithinAt.cosh`

English:
theorem DifferentiableWithinAt.cosh
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.cosh.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.cosh
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.cosh.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.cosh.differentiableWithinAt
-/
theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.cosh.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.cosh` / 定理 `DifferentiableAt.cosh`

English:
theorem DifferentiableAt.cosh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.cosh.differentiableAt

中文:
定理 DifferentiableAt.cosh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.cosh.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.cosh.differentiableAt
-/
theorem DifferentiableAt.cosh (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => Real.cosh (f x)) x :=
  hc.hasFDerivAt.cosh.differentiableAt

/--
theorem `DifferentiableOn.cosh` / 定理 `DifferentiableOn.cosh`

English:
theorem DifferentiableOn.cosh
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).cosh

@[simp, fun_prop]

中文:
定理 DifferentiableOn.cosh
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).cosh

@[simp, fun_prop]
-/
theorem DifferentiableOn.cosh (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh

@[simp, fun_prop]
/--
theorem `Differentiable.cosh` / 定理 `Differentiable.cosh`

English:
theorem Differentiable.cosh
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => Real.cosh (f x)
  proof: fun x => (hc x).cosh

中文:
定理 可微.cosh
  条件: (hc : 可微 实数 f)
  结论: 可微 实数 fun x => 实数.cosh (f x)
  证明: fun x => (hc x).cosh
-/
theorem Differentiable.cosh (hc : Differentiable Real f) : Differentiable Real fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh

/--
theorem `fderivWithin_cosh` / 定理 `fderivWithin_cosh`

English:
theorem fderivWithin_cosh
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.cosh.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_cosh
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.cosh.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.cosh.fderivWithin
-/
theorem fderivWithin_cosh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.cosh.fderivWithin hxs

@[simp]
/--
theorem `fderiv_cosh` / 定理 `fderiv_cosh`

English:
theorem fderiv_cosh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.cosh.fderiv

中文:
定理 fderiv_cosh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.cosh.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.cosh.fderiv
-/
theorem fderiv_cosh (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv Real f x :=
  hc.hasFDerivAt.cosh.fderiv

/--
theorem `ContDiff.cosh` / 定理 `ContDiff.cosh`

English:
theorem ContDiff.cosh
  given: {n} (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => Real.cosh (f x)
  proof: Real.contDiff_cosh.comp h

中文:
定理 连续可微.cosh
  条件: {n} (h : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => 实数.cosh (f x)
  证明: Real.contDiff_cosh.comp h

Depends on / 依赖: Real.contDiff_cosh.comp, contDiff_cosh
-/
theorem ContDiff.cosh {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.cosh (f x) :=
  Real.contDiff_cosh.comp h

/--
theorem `ContDiffAt.cosh` / 定理 `ContDiffAt.cosh`

English:
theorem ContDiffAt.cosh
  given: {n} (hf : ContDiffAt Real n f x)
  proof: Real.contDiff_cosh.contDiffAt.comp x hf

中文:
定理 ContDiffAt.cosh
  条件: {n} (hf : ContDiffAt 实数 n f x)
  证明: Real.contDiff_cosh.contDiffAt.comp x hf

Depends on / 依赖: Real.contDiff_cosh.contDiffAt.comp, contDiffAt, contDiff_cosh
-/
theorem ContDiffAt.cosh {n} (hf : ContDiffAt Real n f x) :
    ContDiffAt Real n (fun x => Real.cosh (f x)) x :=
  Real.contDiff_cosh.contDiffAt.comp x hf

/--
theorem `ContDiffOn.cosh` / 定理 `ContDiffOn.cosh`

English:
theorem ContDiffOn.cosh
  given: {n} (hf : ContDiffOn Real n f s)
  proof: Real.contDiff_cosh.comp_contDiffOn hf

中文:
定理 ContDiffOn.cosh
  条件: {n} (hf : ContDiffOn 实数 n f s)
  证明: Real.contDiff_cosh.comp_contDiffOn hf

Depends on / 依赖: Real.contDiff_cosh.comp_contDiffOn, comp_contDiffOn, contDiff_cosh
-/
theorem ContDiffOn.cosh {n} (hf : ContDiffOn Real n f s) :
    ContDiffOn Real n (fun x => Real.cosh (f x)) s :=
  Real.contDiff_cosh.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.cosh` / 定理 `ContDiffWithinAt.cosh`

English:
theorem ContDiffWithinAt.cosh
  given: {n} (hf : ContDiffWithinAt Real n f s x)
  proof: Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.cosh
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x)
  证明: Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_cosh
-/
theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => Real.cosh (f x)) s x :=
  Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf


/--
theorem `HasStrictFDerivAt.sinh` / 定理 `HasStrictFDerivAt.sinh`

English:
theorem HasStrictFDerivAt.sinh
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.sinh
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Real.hasStrictDerivAt_sinh, comp_hasStrictFDerivAt, hasStrictDerivAt_sinh
-/
theorem HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.sinh` / 定理 `HasFDerivAt.sinh`

English:
theorem HasFDerivAt.sinh
  given: (hf : HasFDerivAt f f' x)
  proof: (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.sinh
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Real.hasDerivAt_sinh, comp_hasFDerivAt, hasDerivAt_sinh
-/
theorem HasFDerivAt.sinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.sinh` / 定理 `HasFDerivWithinAt.sinh`

English:
theorem HasFDerivWithinAt.sinh
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.sinh
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_sinh, comp_hasFDerivWithinAt, hasDerivAt_sinh
-/
theorem HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.sinh` / 定理 `DifferentiableWithinAt.sinh`

English:
theorem DifferentiableWithinAt.sinh
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.sinh.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.sinh
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.sinh.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.sinh.differentiableWithinAt
-/
theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.sinh.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.sinh` / 定理 `DifferentiableAt.sinh`

English:
theorem DifferentiableAt.sinh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.sinh.differentiableAt

中文:
定理 DifferentiableAt.sinh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.sinh.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.sinh.differentiableAt
-/
theorem DifferentiableAt.sinh (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => Real.sinh (f x)) x :=
  hc.hasFDerivAt.sinh.differentiableAt

/--
theorem `DifferentiableOn.sinh` / 定理 `DifferentiableOn.sinh`

English:
theorem DifferentiableOn.sinh
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).sinh

@[simp, fun_prop]

中文:
定理 DifferentiableOn.sinh
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).sinh

@[simp, fun_prop]
-/
theorem DifferentiableOn.sinh (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh

@[simp, fun_prop]
/--
theorem `Differentiable.sinh` / 定理 `Differentiable.sinh`

English:
theorem Differentiable.sinh
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => Real.sinh (f x)
  proof: fun x => (hc x).sinh

中文:
定理 可微.sinh
  条件: (hc : 可微 实数 f)
  结论: 可微 实数 fun x => 实数.sinh (f x)
  证明: fun x => (hc x).sinh
-/
theorem Differentiable.sinh (hc : Differentiable Real f) : Differentiable Real fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh

/--
theorem `fderivWithin_sinh` / 定理 `fderivWithin_sinh`

English:
theorem fderivWithin_sinh
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.sinh.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_sinh
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.sinh.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.sinh.fderivWithin
-/
theorem fderivWithin_sinh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.sinh.fderivWithin hxs

@[simp]
/--
theorem `fderiv_sinh` / 定理 `fderiv_sinh`

English:
theorem fderiv_sinh
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.sinh.fderiv

中文:
定理 fderiv_sinh
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.sinh.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.sinh.fderiv
-/
theorem fderiv_sinh (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv Real f x :=
  hc.hasFDerivAt.sinh.fderiv

/--
theorem `ContDiff.sinh` / 定理 `ContDiff.sinh`

English:
theorem ContDiff.sinh
  given: {n} (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => Real.sinh (f x)
  proof: Real.contDiff_sinh.comp h

中文:
定理 连续可微.sinh
  条件: {n} (h : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => 实数.sinh (f x)
  证明: Real.contDiff_sinh.comp h

Depends on / 依赖: Real.contDiff_sinh.comp, contDiff_sinh
-/
theorem ContDiff.sinh {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.sinh (f x) :=
  Real.contDiff_sinh.comp h

/--
theorem `ContDiffAt.sinh` / 定理 `ContDiffAt.sinh`

English:
theorem ContDiffAt.sinh
  given: {n} (hf : ContDiffAt Real n f x)
  proof: Real.contDiff_sinh.contDiffAt.comp x hf

中文:
定理 ContDiffAt.sinh
  条件: {n} (hf : ContDiffAt 实数 n f x)
  证明: Real.contDiff_sinh.contDiffAt.comp x hf

Depends on / 依赖: Real.contDiff_sinh.contDiffAt.comp, contDiffAt, contDiff_sinh
-/
theorem ContDiffAt.sinh {n} (hf : ContDiffAt Real n f x) :
    ContDiffAt Real n (fun x => Real.sinh (f x)) x :=
  Real.contDiff_sinh.contDiffAt.comp x hf

/--
theorem `ContDiffOn.sinh` / 定理 `ContDiffOn.sinh`

English:
theorem ContDiffOn.sinh
  given: {n} (hf : ContDiffOn Real n f s)
  proof: Real.contDiff_sinh.comp_contDiffOn hf

中文:
定理 ContDiffOn.sinh
  条件: {n} (hf : ContDiffOn 实数 n f s)
  证明: Real.contDiff_sinh.comp_contDiffOn hf

Depends on / 依赖: Real.contDiff_sinh.comp_contDiffOn, comp_contDiffOn, contDiff_sinh
-/
theorem ContDiffOn.sinh {n} (hf : ContDiffOn Real n f s) :
    ContDiffOn Real n (fun x => Real.sinh (f x)) s :=
  Real.contDiff_sinh.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.sinh` / 定理 `ContDiffWithinAt.sinh`

English:
theorem ContDiffWithinAt.sinh
  given: {n} (hf : ContDiffWithinAt Real n f s x)
  proof: Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.sinh
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x)
  证明: Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_sinh
-/
theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => Real.sinh (f x)) s x :=
  Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

@[simp]
/--
theorem `Complex.logDeriv_cosh` / 定理 `Complex.logDeriv_cosh`

English:
theorem Complex.logDeriv_cosh
  statement: logDeriv (Complex.cosh) = Complex.tanh
  proof: by
  ext
  rw [logDeriv]; rw [Complex.deriv_cosh]; rw [Pi.div_apply]; rw [Complex.tanh]

@[simp]

中文:
定理 复形.logDeriv_cosh
  结论: logDeriv (复形.cosh) = 复形.tanh
  证明: by
  ext
  rw [logDeriv]; rw [Complex.deriv_cosh]; rw [Pi.div_apply]; rw [Complex.tanh]

@[simp]

Depends on / 依赖: Complex.deriv_cosh, Complex.tanh, Pi.div_apply, deriv_cosh, div_apply, logDeriv
-/
theorem Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh := by
  ext
  rw [logDeriv]; rw [Complex.deriv_cosh]; rw [Pi.div_apply]; rw [Complex.tanh]

@[simp]
/--
theorem `Real.logDeriv_cosh` / 定理 `Real.logDeriv_cosh`

English:
theorem Real.logDeriv_cosh
  statement: logDeriv (Real.cosh) = Real.tanh
  proof: by
  ext
  rw [logDeriv]; rw [Real.deriv_cosh]; rw [Pi.div_apply]; rw [Real.tanh_eq_sinh_div_cosh]

中文:
定理 实数.logDeriv_cosh
  结论: logDeriv (实数.cosh) = 实数.tanh
  证明: by
  ext
  rw [logDeriv]; rw [Real.deriv_cosh]; rw [Pi.div_apply]; rw [Real.tanh_eq_sinh_div_cosh]

Depends on / 依赖: Pi.div_apply, Real.deriv_cosh, Real.tanh_eq_sinh_div_cosh, deriv_cosh, div_apply, logDeriv, tanh_eq_sinh_div_cosh
-/
theorem Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh := by
  ext
  rw [logDeriv]; rw [Real.deriv_cosh]; rw [Pi.div_apply]; rw [Real.tanh_eq_sinh_div_cosh]

end LogDeriv

end

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
meta def evalSinh : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  let zα : Q(Zero Real) := q(inferInstance)
  let pα : Q(PartialOrder Real) := q(inferInstance)
  match u, α, e with
  | 0, ~q(Real), ~q(Real.sinh $a) =>
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => return .positive q(sinh_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(sinh_nonneg_of_nonneg $pa)
    | .nonzero pa => return .nonzero q(sinh_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not Real.sinh"

example (x : Real) (hx : 0 < x) : 0 < x.sinh := by positivity
example (x : Real) (hx : 0 <= x) : 0 <= x.sinh := by positivity
example (x : Real) (hx : x != 0) : x.sinh != 0 := by positivity

end Mathlib.Meta.Positivity
