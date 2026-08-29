/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/--
theorem `hasStrictDerivAt_sin` / 定理 `hasStrictDerivAt_sin`

English:
theorem hasStrictDerivAt_sin
  given: (x : Complex)
  statement: HasStrictDerivAt sin (cos x) x
  proof: by
  simp only [cos, div_eq_mul_inv]
  convert!
    ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
              ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  rw [sub_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [I

中文:
定理 hasStrictDerivAt_sin
  条件: (x : Complex)
  结论: HasStrictDerivAt sin (cos x) x
  证明: by
  simp only [cos, div_eq_mul_inv]
  convert!
    ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
              ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  rw [sub_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [I

Depends on / 依赖: I_mul_I, add_comm, cexp.sub, convert, div_eq_mul_inv, fun_neg, fun_neg.mul_const, hasStrictDerivAt_id, mul_assoc, mul_const, mul_neg_one, mul_one, neg_neg, neg_one_mul, one_mul, sub_mul, sub_neg_eq_add
-/
theorem hasStrictDerivAt_sin (x : Complex) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert!
    ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
              ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  rw [sub_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [I_mul_I]; rw [neg_one_mul]; rw [neg_neg]; rw [mul_one]; rw [one_mul]; rw [mul_assoc]; rw [I_mul_I]; rw [mul_neg_one]; rw [sub_neg_eq_add]; rw [add_comm]

/--
theorem `hasDerivAt_sin` / 定理 `hasDerivAt_sin`

English:
theorem hasDerivAt_sin
  given: (x : Complex)
  statement: HasDerivAt sin (cos x) x
  proof: (hasStrictDerivAt_sin x).hasDerivAt

中文:
定理 hasDerivAt_sin
  条件: (x : Complex)
  结论: HasDerivAt sin (cos x) x
  证明: (hasStrictDerivAt_sin x).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_sin
-/
theorem hasDerivAt_sin (x : Complex) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

/--
theorem `isEquivalent_sin` / 定理 `isEquivalent_sin`

English:
theorem isEquivalent_sin
  statement: sin ~[𝓝 0] id
  proof: by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]

中文:
定理 isEquivalent_sin
  结论: sin ~[𝓝 0] id
  证明: by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]

Depends on / 依赖: hasDerivAt_sin, isLittleO
-/
theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]
/--
theorem `contDiff_sin` / 定理 `contDiff_sin`

English:
theorem contDiff_sin
  given: {n}
  statement: ContDiff Complex n sin
  proof: (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _

@[simp]

中文:
定理 contDiff_sin
  条件: {n}
  结论: ContDiff Complex n sin
  证明: (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _

@[simp]

Depends on / 依赖: cexp.sub, contDiff_const, contDiff_id, contDiff_id.mul, contDiff_neg, contDiff_neg.mul, div_const
-/
theorem contDiff_sin {n} : ContDiff Complex n sin :=
  (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _

@[simp]
/--
theorem `differentiable_sin` / 定理 `differentiable_sin`

English:
theorem differentiable_sin
  statement: Differentiable Complex sin
  proof: fun x => (hasDerivAt_sin x).differentiableAt

@[simp]

中文:
定理 differentiable_sin
  结论: Differentiable Complex sin
  证明: fun x => (hasDerivAt_sin x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_sin
-/
theorem differentiable_sin : Differentiable Complex sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
/--
theorem `differentiableAt_sin` / 定理 `differentiableAt_sin`

English:
theorem differentiableAt_sin
  given: {x : Complex}
  statement: DifferentiableAt Complex sin x
  proof: differentiable_sin x

中文:
定理 differentiableAt_sin
  条件: {x : Complex}
  结论: DifferentiableAt Complex sin x
  证明: differentiable_sin x

Depends on / 依赖: differentiable_sin
-/
theorem differentiableAt_sin {x : Complex} : DifferentiableAt Complex sin x :=
  differentiable_sin x

/-- The function `Complex.sin` is complex analytic. -/
@[fun_prop]
/--
lemma `analyticAt_sin` / 引理 `analyticAt_sin`

English:
lemma analyticAt_sin
  given: {x : Complex}
  statement: AnalyticAt Complex sin x
  proof: contDiff_sin.contDiffAt.analyticAt

中文:
引理 analyticAt_sin
  条件: {x : Complex}
  结论: AnalyticAt Complex sin x
  证明: contDiff_sin.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_sin, contDiff_sin.contDiffAt.analyticAt
-/
lemma analyticAt_sin {x : Complex} : AnalyticAt Complex sin x :=
  contDiff_sin.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_sin` / 引理 `analyticWithinAt_sin`

English:
lemma analyticWithinAt_sin
  given: {x : Complex} {s : Set Complex}
  statement: AnalyticWithinAt Complex sin s x
  proof: contDiff_sin.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_sin
  条件: {x : Complex} {s : Set Complex}
  结论: AnalyticWithinAt Complex sin s x
  证明: contDiff_sin.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_sin, contDiff_sin.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_sin {x : Complex} {s : Set Complex} : AnalyticWithinAt Complex sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_sin` / 定理 `analyticOnNhd_sin`

English:
theorem analyticOnNhd_sin
  given: {s : Set Complex}
  statement: AnalyticOnNhd Complex sin s
  proof: fun _ _ => analyticAt_sin

中文:
定理 analyticOnNhd_sin
  条件: {s : Set Complex}
  结论: AnalyticOnNhd Complex sin s
  证明: fun _ _ => analyticAt_sin

Depends on / 依赖: analyticAt_sin
-/
theorem analyticOnNhd_sin {s : Set Complex} : AnalyticOnNhd Complex sin s :=
  fun _ _ => analyticAt_sin

/--
lemma `analyticOn_sin` / 引理 `analyticOn_sin`

English:
lemma analyticOn_sin
  given: {s : Set Complex}
  statement: AnalyticOn Complex sin s
  proof: contDiff_sin.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_sin
  条件: {s : Set Complex}
  结论: AnalyticOn Complex sin s
  证明: contDiff_sin.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_sin, contDiff_sin.contDiffOn.analyticOn
-/
lemma analyticOn_sin {s : Set Complex} : AnalyticOn Complex sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_sin` / 定理 `deriv_sin`

English:
theorem deriv_sin
  statement: deriv sin = cos
  proof: funext fun x => (hasDerivAt_sin x).deriv

中文:
定理 deriv_sin
  结论: deriv sin = cos
  证明: funext fun x => (hasDerivAt_sin x).deriv

Depends on / 依赖: hasDerivAt_sin
-/
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv

/--
theorem `hasStrictDerivAt_cos` / 定理 `hasStrictDerivAt_cos`

English:
theorem hasStrictDerivAt_cos
  given: (x : Complex)
  statement: HasStrictDerivAt cos (-sin x) x
  proof: by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert!
    (((hasStrictDerivAt_id x).mul_const I).cexp.add
          ((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  ring

中文:
定理 hasStrictDerivAt_cos
  条件: (x : Complex)
  结论: HasStrictDerivAt cos (-sin x) x
  证明: by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert!
    (((hasStrictDerivAt_id x).mul_const I).cexp.add
          ((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  ring

Depends on / 依赖: cexp.add, convert, div_eq_mul_inv, fun_neg, fun_neg.mul_const, hasStrictDerivAt_id, mul_const, neg_mul_eq_neg_mul
-/
theorem hasStrictDerivAt_cos (x : Complex) : HasStrictDerivAt cos (-sin x) x := by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert!
    (((hasStrictDerivAt_id x).mul_const I).cexp.add
          ((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp).mul_const
      (2 : Complex)⁻¹ using 1
  simp only [id]
  ring

/--
theorem `hasDerivAt_cos` / 定理 `hasDerivAt_cos`

English:
theorem hasDerivAt_cos
  given: (x : Complex)
  statement: HasDerivAt cos (-sin x) x
  proof: (hasStrictDerivAt_cos x).hasDerivAt

@[fun_prop]

中文:
定理 hasDerivAt_cos
  条件: (x : Complex)
  结论: HasDerivAt cos (-sin x) x
  证明: (hasStrictDerivAt_cos x).hasDerivAt

@[fun_prop]

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_cos
-/
theorem hasDerivAt_cos (x : Complex) : HasDerivAt cos (-sin x) x :=
  (hasStrictDerivAt_cos x).hasDerivAt

@[fun_prop]
/--
theorem `contDiff_cos` / 定理 `contDiff_cos`

English:
theorem contDiff_cos
  given: {n}
  statement: ContDiff Complex n cos
  proof: ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _

@[simp]

中文:
定理 contDiff_cos
  条件: {n}
  结论: ContDiff Complex n cos
  证明: ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _

@[simp]

Depends on / 依赖: cexp.add, contDiff_const, contDiff_id, contDiff_id.mul, contDiff_neg, contDiff_neg.mul, div_const
-/
theorem contDiff_cos {n} : ContDiff Complex n cos :=
  ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _

@[simp]
/--
theorem `differentiable_cos` / 定理 `differentiable_cos`

English:
theorem differentiable_cos
  statement: Differentiable Complex cos
  proof: fun x => (hasDerivAt_cos x).differentiableAt

@[simp]

中文:
定理 differentiable_cos
  结论: Differentiable Complex cos
  证明: fun x => (hasDerivAt_cos x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_cos
-/
theorem differentiable_cos : Differentiable Complex cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
/--
theorem `differentiableAt_cos` / 定理 `differentiableAt_cos`

English:
theorem differentiableAt_cos
  given: {x : Complex}
  statement: DifferentiableAt Complex cos x
  proof: differentiable_cos x

中文:
定理 differentiableAt_cos
  条件: {x : Complex}
  结论: DifferentiableAt Complex cos x
  证明: differentiable_cos x

Depends on / 依赖: differentiable_cos
-/
theorem differentiableAt_cos {x : Complex} : DifferentiableAt Complex cos x :=
  differentiable_cos x

/-- The function `Complex.cos` is complex analytic. -/
@[fun_prop]
/--
lemma `analyticAt_cos` / 引理 `analyticAt_cos`

English:
lemma analyticAt_cos
  given: {x : Complex}
  statement: AnalyticAt Complex cos x
  proof: contDiff_cos.contDiffAt.analyticAt

中文:
引理 analyticAt_cos
  条件: {x : Complex}
  结论: AnalyticAt Complex cos x
  证明: contDiff_cos.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_cos, contDiff_cos.contDiffAt.analyticAt
-/
lemma analyticAt_cos {x : Complex} : AnalyticAt Complex cos x :=
  contDiff_cos.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_cos` / 引理 `analyticWithinAt_cos`

English:
lemma analyticWithinAt_cos
  given: {x : Complex} {s : Set Complex}
  statement: AnalyticWithinAt Complex cos s x
  proof: contDiff_cos.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_cos
  条件: {x : Complex} {s : Set Complex}
  结论: AnalyticWithinAt Complex cos s x
  证明: contDiff_cos.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_cos, contDiff_cos.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_cos {x : Complex} {s : Set Complex} : AnalyticWithinAt Complex cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_cos` / 定理 `analyticOnNhd_cos`

English:
theorem analyticOnNhd_cos
  given: {s : Set Complex}
  statement: AnalyticOnNhd Complex cos s
  proof: fun _ _ => analyticAt_cos

中文:
定理 analyticOnNhd_cos
  条件: {s : Set Complex}
  结论: AnalyticOnNhd Complex cos s
  证明: fun _ _ => analyticAt_cos

Depends on / 依赖: analyticAt_cos
-/
theorem analyticOnNhd_cos {s : Set Complex} : AnalyticOnNhd Complex cos s :=
  fun _ _ => analyticAt_cos

/--
lemma `analyticOn_cos` / 引理 `analyticOn_cos`

English:
lemma analyticOn_cos
  given: {s : Set Complex}
  statement: AnalyticOn Complex cos s
  proof: contDiff_cos.contDiffOn.analyticOn

中文:
引理 analyticOn_cos
  条件: {s : Set Complex}
  结论: AnalyticOn Complex cos s
  证明: contDiff_cos.contDiffOn.analyticOn

Depends on / 依赖: analyticOn, contDiffOn, contDiff_cos, contDiff_cos.contDiffOn.analyticOn
-/
lemma analyticOn_cos {s : Set Complex} : AnalyticOn Complex cos s :=
  contDiff_cos.contDiffOn.analyticOn

/--
theorem `deriv_cos` / 定理 `deriv_cos`

English:
theorem deriv_cos
  given: {x : Complex}
  statement: deriv cos x = -sin x
  proof: (hasDerivAt_cos x).deriv

@[simp]

中文:
定理 deriv_cos
  条件: {x : Complex}
  结论: deriv cos x = -sin x
  证明: (hasDerivAt_cos x).deriv

@[simp]

Depends on / 依赖: hasDerivAt_cos
-/
theorem deriv_cos {x : Complex} : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
/--
theorem `deriv_cos'` / 定理 `deriv_cos'`

English:
theorem deriv_cos'
  statement: deriv cos = fun x => -sin x
  proof: funext fun _ => deriv_cos

中文:
定理 deriv_cos'
  结论: deriv cos = fun x => -sin x
  证明: funext fun _ => deriv_cos

Depends on / 依赖: deriv_cos
-/
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/


variable {f : Complex -> Complex} {f' x : Complex} {s : Set Complex}



/--
theorem `HasStrictDerivAt.ccos` / 定理 `HasStrictDerivAt.ccos`

English:
theorem HasStrictDerivAt.ccos
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_cos (f x)).comp x hf

中文:
定理 HasStrictDerivAt.ccos
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_cos (f x)).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cos, hasStrictDerivAt_cos
-/
theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp x hf

/--
theorem `HasDerivAt.ccos` / 定理 `HasDerivAt.ccos`

English:
theorem HasDerivAt.ccos
  given: (hf : HasDerivAt f f' x)
  proof: (Complex.hasDerivAt_cos (f x)).comp x hf

中文:
定理 HasDerivAt.ccos
  条件: (hf : HasDerivAt f f' x)
  证明: (Complex.hasDerivAt_cos (f x)).comp x hf

Depends on / 依赖: Complex.hasDerivAt_cos, hasDerivAt_cos
-/
theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasDerivAt_cos (f x)).comp x hf

/--
theorem `HasDerivWithinAt.ccos` / 定理 `HasDerivWithinAt.ccos`

English:
theorem HasDerivWithinAt.ccos
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.ccos
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_cos, comp_hasDerivWithinAt, hasDerivAt_cos
-/
theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_ccos` / 定理 `derivWithin_ccos`

English:
theorem derivWithin_ccos
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasDerivWithinAt.ccos.derivWithin hxs

@[simp]

中文:
定理 derivWithin_ccos
  条件: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  证明: hf.hasDerivWithinAt.ccos.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.ccos.derivWithin
-/
theorem derivWithin_ccos (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccos.derivWithin hxs

@[simp]
/--
theorem `deriv_ccos` / 定理 `deriv_ccos`

English:
theorem deriv_ccos
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasDerivAt.ccos.deriv

中文:
定理 deriv_ccos
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasDerivAt.ccos.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.ccos.deriv
-/
theorem deriv_ccos (hc : DifferentiableAt Complex f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.hasDerivAt.ccos.deriv



/--
theorem `HasStrictDerivAt.csin` / 定理 `HasStrictDerivAt.csin`

English:
theorem HasStrictDerivAt.csin
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_sin (f x)).comp x hf

中文:
定理 HasStrictDerivAt.csin
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_sin (f x)).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_sin, hasStrictDerivAt_sin
-/
theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp x hf

/--
theorem `HasDerivAt.csin` / 定理 `HasDerivAt.csin`

English:
theorem HasDerivAt.csin
  given: (hf : HasDerivAt f f' x)
  proof: (Complex.hasDerivAt_sin (f x)).comp x hf

中文:
定理 HasDerivAt.csin
  条件: (hf : HasDerivAt f f' x)
  证明: (Complex.hasDerivAt_sin (f x)).comp x hf

Depends on / 依赖: Complex.hasDerivAt_sin, hasDerivAt_sin
-/
theorem HasDerivAt.csin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasDerivAt_sin (f x)).comp x hf

/--
theorem `HasDerivWithinAt.csin` / 定理 `HasDerivWithinAt.csin`

English:
theorem HasDerivWithinAt.csin
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.csin
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_sin, comp_hasDerivWithinAt, hasDerivAt_sin
-/
theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_csin` / 定理 `derivWithin_csin`

English:
theorem derivWithin_csin
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasDerivWithinAt.csin.derivWithin hxs

@[simp]

中文:
定理 derivWithin_csin
  条件: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  证明: hf.hasDerivWithinAt.csin.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.csin.derivWithin
-/
theorem derivWithin_csin (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csin.derivWithin hxs

@[simp]
/--
theorem `deriv_csin` / 定理 `deriv_csin`

English:
theorem deriv_csin
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasDerivAt.csin.deriv

中文:
定理 deriv_csin
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasDerivAt.csin.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.csin.deriv
-/
theorem deriv_csin (hc : DifferentiableAt Complex f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.hasDerivAt.csin.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {f : E -> Complex} {f' : StrongDual Complex E}
  {x : E} {s : Set E}



/--
theorem `HasStrictFDerivAt.ccos` / 定理 `HasStrictFDerivAt.ccos`

English:
theorem HasStrictFDerivAt.ccos
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.ccos
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cos, comp_hasStrictFDerivAt, hasStrictDerivAt_cos
-/
theorem HasStrictFDerivAt.ccos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.ccos` / 定理 `HasFDerivAt.ccos`

English:
theorem HasFDerivAt.ccos
  given: (hf : HasFDerivAt f f' x)
  proof: (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

中文:
定理 HasFDerivAt.ccos
  条件: (hf : HasFDerivAt f f' x)
  证明: (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Complex.hasDerivAt_cos, comp_hasFDerivAt, hasDerivAt_cos
-/
theorem HasFDerivAt.ccos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.ccos` / 定理 `HasFDerivWithinAt.ccos`

English:
theorem HasFDerivWithinAt.ccos
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.ccos
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_cos, comp_hasFDerivWithinAt, hasDerivAt_cos
-/
theorem HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.ccos` / 定理 `DifferentiableWithinAt.ccos`

English:
theorem DifferentiableWithinAt.ccos
  given: (hf : DifferentiableWithinAt Complex f s x)
  proof: hf.hasFDerivWithinAt.ccos.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.ccos
  条件: (hf : DifferentiableWithinAt Complex f s x)
  证明: hf.hasFDerivWithinAt.ccos.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.ccos.differentiableWithinAt
-/
theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt Complex f s x) :
    DifferentiableWithinAt Complex (fun x => Complex.cos (f x)) s x :=
  hf.hasFDerivWithinAt.ccos.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.ccos` / 定理 `DifferentiableAt.ccos`

English:
theorem DifferentiableAt.ccos
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.ccos.differentiableAt

中文:
定理 DifferentiableAt.ccos
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasFDerivAt.ccos.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.ccos.differentiableAt
-/
theorem DifferentiableAt.ccos (hc : DifferentiableAt Complex f x) :
    DifferentiableAt Complex (fun x => Complex.cos (f x)) x :=
  hc.hasFDerivAt.ccos.differentiableAt

/--
theorem `DifferentiableOn.ccos` / 定理 `DifferentiableOn.ccos`

English:
theorem DifferentiableOn.ccos
  given: (hc : DifferentiableOn Complex f s)
  proof: fun x h => (hc x h).ccos

@[simp, fun_prop]

中文:
定理 DifferentiableOn.ccos
  条件: (hc : DifferentiableOn Complex f s)
  证明: fun x h => (hc x h).ccos

@[simp, fun_prop]
-/
theorem DifferentiableOn.ccos (hc : DifferentiableOn Complex f s) :
    DifferentiableOn Complex (fun x => Complex.cos (f x)) s := fun x h => (hc x h).ccos

@[simp, fun_prop]
/--
theorem `Differentiable.ccos` / 定理 `Differentiable.ccos`

English:
theorem Differentiable.ccos
  given: (hc : Differentiable Complex f)
  proof: fun x => (hc x).ccos

中文:
定理 Differentiable.ccos
  条件: (hc : Differentiable Complex f)
  证明: fun x => (hc x).ccos
-/
theorem Differentiable.ccos (hc : Differentiable Complex f) :
    Differentiable Complex fun x => Complex.cos (f x) := fun x => (hc x).ccos

/--
theorem `fderivWithin_ccos` / 定理 `fderivWithin_ccos`

English:
theorem fderivWithin_ccos
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasFDerivWithinAt.ccos.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_ccos
  条件: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  证明: hf.hasFDerivWithinAt.ccos.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.ccos.fderivWithin
-/
theorem fderivWithin_ccos (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    fderivWithin Complex (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin Complex f s x :=
  hf.hasFDerivWithinAt.ccos.fderivWithin hxs

@[simp]
/--
theorem `fderiv_ccos` / 定理 `fderiv_ccos`

English:
theorem fderiv_ccos
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.ccos.fderiv

中文:
定理 fderiv_ccos
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasFDerivAt.ccos.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.ccos.fderiv
-/
theorem fderiv_ccos (hc : DifferentiableAt Complex f x) :
    fderiv Complex (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv Complex f x :=
  hc.hasFDerivAt.ccos.fderiv

/--
theorem `ContDiff.ccos` / 定理 `ContDiff.ccos`

English:
theorem ContDiff.ccos
  given: {n} (h : ContDiff Complex n f)
  statement: ContDiff Complex n fun x => Complex.cos (f x)
  proof: Complex.contDiff_cos.comp h

中文:
定理 ContDiff.ccos
  条件: {n} (h : ContDiff Complex n f)
  结论: ContDiff Complex n fun x => Complex.cos (f x)
  证明: Complex.contDiff_cos.comp h

Depends on / 依赖: Complex.contDiff_cos.comp, contDiff_cos
-/
theorem ContDiff.ccos {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x => Complex.cos (f x) :=
  Complex.contDiff_cos.comp h

/--
theorem `ContDiffAt.ccos` / 定理 `ContDiffAt.ccos`

English:
theorem ContDiffAt.ccos
  given: {n} (hf : ContDiffAt Complex n f x)
  proof: Complex.contDiff_cos.contDiffAt.comp x hf

中文:
定理 ContDiffAt.ccos
  条件: {n} (hf : ContDiffAt Complex n f x)
  证明: Complex.contDiff_cos.contDiffAt.comp x hf

Depends on / 依赖: Complex.contDiff_cos.contDiffAt.comp, contDiffAt, contDiff_cos
-/
theorem ContDiffAt.ccos {n} (hf : ContDiffAt Complex n f x) :
    ContDiffAt Complex n (fun x => Complex.cos (f x)) x :=
  Complex.contDiff_cos.contDiffAt.comp x hf

/--
theorem `ContDiffOn.ccos` / 定理 `ContDiffOn.ccos`

English:
theorem ContDiffOn.ccos
  given: {n} (hf : ContDiffOn Complex n f s)
  proof: Complex.contDiff_cos.comp_contDiffOn hf

中文:
定理 ContDiffOn.ccos
  条件: {n} (hf : ContDiffOn Complex n f s)
  证明: Complex.contDiff_cos.comp_contDiffOn hf

Depends on / 依赖: Complex.contDiff_cos.comp_contDiffOn, comp_contDiffOn, contDiff_cos
-/
theorem ContDiffOn.ccos {n} (hf : ContDiffOn Complex n f s) :
    ContDiffOn Complex n (fun x => Complex.cos (f x)) s :=
  Complex.contDiff_cos.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.ccos` / 定理 `ContDiffWithinAt.ccos`

English:
theorem ContDiffWithinAt.ccos
  given: {n} (hf : ContDiffWithinAt Complex n f s x)
  proof: Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.ccos
  条件: {n} (hf : ContDiffWithinAt Complex n f s x)
  证明: Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_cos
-/
theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt Complex n f s x) :
    ContDiffWithinAt Complex n (fun x => Complex.cos (f x)) s x :=
  Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf



/--
theorem `HasStrictFDerivAt.csin` / 定理 `HasStrictFDerivAt.csin`

English:
theorem HasStrictFDerivAt.csin
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.csin
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_sin, comp_hasStrictFDerivAt, hasStrictDerivAt_sin
-/
theorem HasStrictFDerivAt.csin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.csin` / 定理 `HasFDerivAt.csin`

English:
theorem HasFDerivAt.csin
  given: (hf : HasFDerivAt f f' x)
  proof: (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

中文:
定理 HasFDerivAt.csin
  条件: (hf : HasFDerivAt f f' x)
  证明: (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Complex.hasDerivAt_sin, comp_hasFDerivAt, hasDerivAt_sin
-/
theorem HasFDerivAt.csin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.csin` / 定理 `HasFDerivWithinAt.csin`

English:
theorem HasFDerivWithinAt.csin
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.csin
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_sin, comp_hasFDerivWithinAt, hasDerivAt_sin
-/
theorem HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.csin` / 定理 `DifferentiableWithinAt.csin`

English:
theorem DifferentiableWithinAt.csin
  given: (hf : DifferentiableWithinAt Complex f s x)
  proof: hf.hasFDerivWithinAt.csin.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.csin
  条件: (hf : DifferentiableWithinAt Complex f s x)
  证明: hf.hasFDerivWithinAt.csin.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.csin.differentiableWithinAt
-/
theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt Complex f s x) :
    DifferentiableWithinAt Complex (fun x => Complex.sin (f x)) s x :=
  hf.hasFDerivWithinAt.csin.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.csin` / 定理 `DifferentiableAt.csin`

English:
theorem DifferentiableAt.csin
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.csin.differentiableAt

中文:
定理 DifferentiableAt.csin
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasFDerivAt.csin.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.csin.differentiableAt
-/
theorem DifferentiableAt.csin (hc : DifferentiableAt Complex f x) :
    DifferentiableAt Complex (fun x => Complex.sin (f x)) x :=
  hc.hasFDerivAt.csin.differentiableAt

/--
theorem `DifferentiableOn.csin` / 定理 `DifferentiableOn.csin`

English:
theorem DifferentiableOn.csin
  given: (hc : DifferentiableOn Complex f s)
  proof: fun x h => (hc x h).csin

@[simp, fun_prop]

中文:
定理 DifferentiableOn.csin
  条件: (hc : DifferentiableOn Complex f s)
  证明: fun x h => (hc x h).csin

@[simp, fun_prop]
-/
theorem DifferentiableOn.csin (hc : DifferentiableOn Complex f s) :
    DifferentiableOn Complex (fun x => Complex.sin (f x)) s := fun x h => (hc x h).csin

@[simp, fun_prop]
/--
theorem `Differentiable.csin` / 定理 `Differentiable.csin`

English:
theorem Differentiable.csin
  given: (hc : Differentiable Complex f)
  proof: fun x => (hc x).csin

中文:
定理 Differentiable.csin
  条件: (hc : Differentiable Complex f)
  证明: fun x => (hc x).csin
-/
theorem Differentiable.csin (hc : Differentiable Complex f) :
    Differentiable Complex fun x => Complex.sin (f x) := fun x => (hc x).csin

/--
theorem `fderivWithin_csin` / 定理 `fderivWithin_csin`

English:
theorem fderivWithin_csin
  given: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  proof: hf.hasFDerivWithinAt.csin.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_csin
  条件: (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x)
  证明: hf.hasFDerivWithinAt.csin.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.csin.fderivWithin
-/
theorem fderivWithin_csin (hf : DifferentiableWithinAt Complex f s x) (hxs : UniqueDiffWithinAt Complex s x) :
    fderivWithin Complex (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin Complex f s x :=
  hf.hasFDerivWithinAt.csin.fderivWithin hxs

@[simp]
/--
theorem `fderiv_csin` / 定理 `fderiv_csin`

English:
theorem fderiv_csin
  given: (hc : DifferentiableAt Complex f x)
  proof: hc.hasFDerivAt.csin.fderiv

中文:
定理 fderiv_csin
  条件: (hc : DifferentiableAt Complex f x)
  证明: hc.hasFDerivAt.csin.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.csin.fderiv
-/
theorem fderiv_csin (hc : DifferentiableAt Complex f x) :
    fderiv Complex (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv Complex f x :=
  hc.hasFDerivAt.csin.fderiv

/--
theorem `ContDiff.csin` / 定理 `ContDiff.csin`

English:
theorem ContDiff.csin
  given: {n} (h : ContDiff Complex n f)
  statement: ContDiff Complex n fun x => Complex.sin (f x)
  proof: Complex.contDiff_sin.comp h

中文:
定理 ContDiff.csin
  条件: {n} (h : ContDiff Complex n f)
  结论: ContDiff Complex n fun x => Complex.sin (f x)
  证明: Complex.contDiff_sin.comp h

Depends on / 依赖: Complex.contDiff_sin.comp, contDiff_sin
-/
theorem ContDiff.csin {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x => Complex.sin (f x) :=
  Complex.contDiff_sin.comp h

/--
theorem `ContDiffAt.csin` / 定理 `ContDiffAt.csin`

English:
theorem ContDiffAt.csin
  given: {n} (hf : ContDiffAt Complex n f x)
  proof: Complex.contDiff_sin.contDiffAt.comp x hf

中文:
定理 ContDiffAt.csin
  条件: {n} (hf : ContDiffAt Complex n f x)
  证明: Complex.contDiff_sin.contDiffAt.comp x hf

Depends on / 依赖: Complex.contDiff_sin.contDiffAt.comp, contDiffAt, contDiff_sin
-/
theorem ContDiffAt.csin {n} (hf : ContDiffAt Complex n f x) :
    ContDiffAt Complex n (fun x => Complex.sin (f x)) x :=
  Complex.contDiff_sin.contDiffAt.comp x hf

/--
theorem `ContDiffOn.csin` / 定理 `ContDiffOn.csin`

English:
theorem ContDiffOn.csin
  given: {n} (hf : ContDiffOn Complex n f s)
  proof: Complex.contDiff_sin.comp_contDiffOn hf

中文:
定理 ContDiffOn.csin
  条件: {n} (hf : ContDiffOn Complex n f s)
  证明: Complex.contDiff_sin.comp_contDiffOn hf

Depends on / 依赖: Complex.contDiff_sin.comp_contDiffOn, comp_contDiffOn, contDiff_sin
-/
theorem ContDiffOn.csin {n} (hf : ContDiffOn Complex n f s) :
    ContDiffOn Complex n (fun x => Complex.sin (f x)) s :=
  Complex.contDiff_sin.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.csin` / 定理 `ContDiffWithinAt.csin`

English:
theorem ContDiffWithinAt.csin
  given: {n} (hf : ContDiffWithinAt Complex n f s x)
  proof: Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.csin
  条件: {n} (hf : ContDiffWithinAt Complex n f s x)
  证明: Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_sin
-/
theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt Complex n f s x) :
    ContDiffWithinAt Complex n (fun x => Complex.sin (f x)) s x :=
  Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y z : Real}

/--
theorem `hasStrictDerivAt_sin` / 定理 `hasStrictDerivAt_sin`

English:
theorem hasStrictDerivAt_sin
  given: (x : Real)
  statement: HasStrictDerivAt sin (cos x) x
  proof: (Complex.hasStrictDerivAt_sin x).real_of_complex

中文:
定理 hasStrictDerivAt_sin
  条件: (x : 实数)
  结论: HasStrictDerivAt sin (cos x) x
  证明: (Complex.hasStrictDerivAt_sin x).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_sin, hasStrictDerivAt_sin, real_of_complex
-/
theorem hasStrictDerivAt_sin (x : Real) : HasStrictDerivAt sin (cos x) x :=
  (Complex.hasStrictDerivAt_sin x).real_of_complex

/--
theorem `hasDerivAt_sin` / 定理 `hasDerivAt_sin`

English:
theorem hasDerivAt_sin
  given: (x : Real)
  statement: HasDerivAt sin (cos x) x
  proof: (hasStrictDerivAt_sin x).hasDerivAt

中文:
定理 hasDerivAt_sin
  条件: (x : 实数)
  结论: HasDerivAt sin (cos x) x
  证明: (hasStrictDerivAt_sin x).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_sin
-/
theorem hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt

/--
theorem `isEquivalent_sin` / 定理 `isEquivalent_sin`

English:
theorem isEquivalent_sin
  statement: sin ~[𝓝 0] id
  proof: by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]

中文:
定理 isEquivalent_sin
  结论: sin ~[𝓝 0] id
  证明: by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]

Depends on / 依赖: hasDerivAt_sin, isLittleO
-/
theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]
/--
theorem `contDiff_sin` / 定理 `contDiff_sin`

English:
theorem contDiff_sin
  given: {n}
  statement: ContDiff Real n sin
  proof: Complex.contDiff_sin.real_of_complex

@[simp]

中文:
定理 contDiff_sin
  条件: {n}
  结论: ContDiff 实数 n sin
  证明: Complex.contDiff_sin.real_of_complex

@[simp]

Depends on / 依赖: Complex.contDiff_sin.real_of_complex, contDiff_sin, real_of_complex
-/
theorem contDiff_sin {n} : ContDiff Real n sin :=
  Complex.contDiff_sin.real_of_complex

@[simp]
/--
theorem `differentiable_sin` / 定理 `differentiable_sin`

English:
theorem differentiable_sin
  statement: Differentiable Real sin
  proof: fun x => (hasDerivAt_sin x).differentiableAt

@[simp]

中文:
定理 differentiable_sin
  结论: Differentiable 实数 sin
  证明: fun x => (hasDerivAt_sin x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_sin
-/
theorem differentiable_sin : Differentiable Real sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
/--
theorem `differentiableAt_sin` / 定理 `differentiableAt_sin`

English:
theorem differentiableAt_sin
  statement: DifferentiableAt Real sin x
  proof: differentiable_sin x

中文:
定理 differentiableAt_sin
  结论: DifferentiableAt 实数 sin x
  证明: differentiable_sin x

Depends on / 依赖: differentiable_sin
-/
theorem differentiableAt_sin : DifferentiableAt Real sin x :=
  differentiable_sin x

/-- The function `Real.sin` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_sin` / 引理 `analyticAt_sin`

English:
lemma analyticAt_sin
  statement: AnalyticAt Real sin x
  proof: contDiff_sin.contDiffAt.analyticAt

中文:
引理 analyticAt_sin
  结论: AnalyticAt 实数 sin x
  证明: contDiff_sin.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_sin, contDiff_sin.contDiffAt.analyticAt
-/
lemma analyticAt_sin : AnalyticAt Real sin x :=
  contDiff_sin.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_sin` / 引理 `analyticWithinAt_sin`

English:
lemma analyticWithinAt_sin
  given: {s : Set Real}
  statement: AnalyticWithinAt Real sin s x
  proof: contDiff_sin.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_sin
  条件: {s : Set 实数}
  结论: AnalyticWithinAt 实数 sin s x
  证明: contDiff_sin.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_sin, contDiff_sin.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_sin {s : Set Real} : AnalyticWithinAt Real sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_sin` / 定理 `analyticOnNhd_sin`

English:
theorem analyticOnNhd_sin
  given: {s : Set Real}
  statement: AnalyticOnNhd Real sin s
  proof: fun _ _ => analyticAt_sin

中文:
定理 analyticOnNhd_sin
  条件: {s : Set 实数}
  结论: AnalyticOnNhd 实数 sin s
  证明: fun _ _ => analyticAt_sin

Depends on / 依赖: analyticAt_sin
-/
theorem analyticOnNhd_sin {s : Set Real} : AnalyticOnNhd Real sin s :=
  fun _ _ => analyticAt_sin

/--
lemma `analyticOn_sin` / 引理 `analyticOn_sin`

English:
lemma analyticOn_sin
  given: {s : Set Real}
  statement: AnalyticOn Real sin s
  proof: contDiff_sin.contDiffOn.analyticOn

@[simp]

中文:
引理 analyticOn_sin
  条件: {s : Set 实数}
  结论: AnalyticOn 实数 sin s
  证明: contDiff_sin.contDiffOn.analyticOn

@[simp]

Depends on / 依赖: analyticOn, contDiffOn, contDiff_sin, contDiff_sin.contDiffOn.analyticOn
-/
lemma analyticOn_sin {s : Set Real} : AnalyticOn Real sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
/--
theorem `deriv_sin` / 定理 `deriv_sin`

English:
theorem deriv_sin
  statement: deriv sin = cos
  proof: funext fun x => (hasDerivAt_sin x).deriv

中文:
定理 deriv_sin
  结论: deriv sin = cos
  证明: funext fun x => (hasDerivAt_sin x).deriv

Depends on / 依赖: hasDerivAt_sin
-/
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv

/--
theorem `hasStrictDerivAt_cos` / 定理 `hasStrictDerivAt_cos`

English:
theorem hasStrictDerivAt_cos
  given: (x : Real)
  statement: HasStrictDerivAt cos (-sin x) x
  proof: (Complex.hasStrictDerivAt_cos x).real_of_complex

中文:
定理 hasStrictDerivAt_cos
  条件: (x : 实数)
  结论: HasStrictDerivAt cos (-sin x) x
  证明: (Complex.hasStrictDerivAt_cos x).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_cos, hasStrictDerivAt_cos, real_of_complex
-/
theorem hasStrictDerivAt_cos (x : Real) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.hasStrictDerivAt_cos x).real_of_complex

/--
theorem `hasDerivAt_cos` / 定理 `hasDerivAt_cos`

English:
theorem hasDerivAt_cos
  given: (x : Real)
  statement: HasDerivAt cos (-sin x) x
  proof: (Complex.hasDerivAt_cos x).real_of_complex

@[fun_prop]

中文:
定理 hasDerivAt_cos
  条件: (x : 实数)
  结论: HasDerivAt cos (-sin x) x
  证明: (Complex.hasDerivAt_cos x).real_of_complex

@[fun_prop]

Depends on / 依赖: Complex.hasDerivAt_cos, hasDerivAt_cos, real_of_complex
-/
theorem hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x) x :=
  (Complex.hasDerivAt_cos x).real_of_complex

@[fun_prop]
/--
theorem `contDiff_cos` / 定理 `contDiff_cos`

English:
theorem contDiff_cos
  given: {n}
  statement: ContDiff Real n cos
  proof: Complex.contDiff_cos.real_of_complex

@[simp]

中文:
定理 contDiff_cos
  条件: {n}
  结论: ContDiff 实数 n cos
  证明: Complex.contDiff_cos.real_of_complex

@[simp]

Depends on / 依赖: Complex.contDiff_cos.real_of_complex, contDiff_cos, real_of_complex
-/
theorem contDiff_cos {n} : ContDiff Real n cos :=
  Complex.contDiff_cos.real_of_complex

@[simp]
/--
theorem `differentiable_cos` / 定理 `differentiable_cos`

English:
theorem differentiable_cos
  statement: Differentiable Real cos
  proof: fun x => (hasDerivAt_cos x).differentiableAt

@[simp]

中文:
定理 differentiable_cos
  结论: Differentiable 实数 cos
  证明: fun x => (hasDerivAt_cos x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_cos
-/
theorem differentiable_cos : Differentiable Real cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
/--
theorem `differentiableAt_cos` / 定理 `differentiableAt_cos`

English:
theorem differentiableAt_cos
  statement: DifferentiableAt Real cos x
  proof: differentiable_cos x

中文:
定理 differentiableAt_cos
  结论: DifferentiableAt 实数 cos x
  证明: differentiable_cos x

Depends on / 依赖: HasFunctorialSurjectiveInjectiveFactorization, differentiable_cos
-/
theorem differentiableAt_cos : DifferentiableAt Real cos x :=
  differentiable_cos x

/-- The function `Real.cos` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_cos` / 引理 `analyticAt_cos`

English:
lemma analyticAt_cos
  statement: AnalyticAt Real cos x
  proof: contDiff_cos.contDiffAt.analyticAt

中文:
引理 analyticAt_cos
  结论: AnalyticAt 实数 cos x
  证明: contDiff_cos.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_cos, contDiff_cos.contDiffAt.analyticAt
-/
lemma analyticAt_cos : AnalyticAt Real cos x :=
  contDiff_cos.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_cos` / 引理 `analyticWithinAt_cos`

English:
lemma analyticWithinAt_cos
  given: {s : Set Real}
  statement: AnalyticWithinAt Real cos s x
  proof: contDiff_cos.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_cos
  条件: {s : Set 实数}
  结论: AnalyticWithinAt 实数 cos s x
  证明: contDiff_cos.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_cos, contDiff_cos.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_cos {s : Set Real} : AnalyticWithinAt Real cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_cos` / 定理 `analyticOnNhd_cos`

English:
theorem analyticOnNhd_cos
  given: {s : Set Real}
  statement: AnalyticOnNhd Real cos s
  proof: fun _ _ => analyticAt_cos

中文:
定理 analyticOnNhd_cos
  条件: {s : Set 实数}
  结论: AnalyticOnNhd 实数 cos s
  证明: fun _ _ => analyticAt_cos

Depends on / 依赖: analyticAt_cos
-/
theorem analyticOnNhd_cos {s : Set Real} : AnalyticOnNhd Real cos s :=
  fun _ _ => analyticAt_cos

/--
lemma `analyticOn_cos` / 引理 `analyticOn_cos`

English:
lemma analyticOn_cos
  given: {s : Set Real}
  statement: AnalyticOn Real cos s
  proof: contDiff_cos.contDiffOn.analyticOn

中文:
引理 analyticOn_cos
  条件: {s : Set 实数}
  结论: AnalyticOn 实数 cos s
  证明: contDiff_cos.contDiffOn.analyticOn

Depends on / 依赖: analyticOn, contDiffOn, contDiff_cos, contDiff_cos.contDiffOn.analyticOn
-/
lemma analyticOn_cos {s : Set Real} : AnalyticOn Real cos s :=
  contDiff_cos.contDiffOn.analyticOn

/--
theorem `deriv_cos` / 定理 `deriv_cos`

English:
theorem deriv_cos
  statement: deriv cos x = -sin x
  proof: (hasDerivAt_cos x).deriv

@[simp]

中文:
定理 deriv_cos
  结论: deriv cos x = -sin x
  证明: (hasDerivAt_cos x).deriv

@[simp]

Depends on / 依赖: hasDerivAt_cos
-/
theorem deriv_cos : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
/--
theorem `deriv_cos'` / 定理 `deriv_cos'`

English:
theorem deriv_cos'
  statement: deriv cos = fun x => -sin x
  proof: funext fun _ => deriv_cos

中文:
定理 deriv_cos'
  结论: deriv cos = fun x => -sin x
  证明: funext fun _ => deriv_cos

Depends on / 依赖: deriv_cos
-/
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sin` and `cos`. -/

namespace Complex

@[simp]
/--
theorem `iteratedDeriv_add_one_sin` / 定理 `iteratedDeriv_add_one_sin`

English:
theorem iteratedDeriv_add_one_sin
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_sin
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_sin (n : Nat) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_add_one_cos` / 定理 `iteratedDeriv_add_one_cos`

English:
theorem iteratedDeriv_add_one_cos
  given: (n : Nat)
  proof: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]

中文:
定理 iteratedDeriv_add_one_cos
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]

Depends on / 依赖: deriv.neg, iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_cos (n : Nat) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]
/--
theorem `iteratedDeriv_even_sin` / 定理 `iteratedDeriv_even_sin`

English:
theorem iteratedDeriv_even_sin
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]

中文:
定理 iteratedDeriv_even_sin
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]

Depends on / 依赖: mul_add, pow_succ
-/
theorem iteratedDeriv_even_sin (n : Nat) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
/--
theorem `iteratedDeriv_even_cos` / 定理 `iteratedDeriv_even_cos`

English:
theorem iteratedDeriv_even_cos
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

中文:
定理 iteratedDeriv_even_cos
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

Depends on / 依赖: mul_add, pow_succ
-/
theorem iteratedDeriv_even_cos (n : Nat) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

/--
theorem `iteratedDeriv_odd_sin` / 定理 `iteratedDeriv_odd_sin`

English:
theorem iteratedDeriv_odd_sin
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_sin
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_sin (n : Nat) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp

/--
theorem `iteratedDeriv_odd_cos` / 定理 `iteratedDeriv_odd_cos`

English:
theorem iteratedDeriv_odd_cos
  given: (n : Nat)
  proof: by simp [pow_succ]

中文:
定理 iteratedDeriv_odd_cos
  条件: (n : 自然数)
  证明: by simp [pow_succ]

Depends on / 依赖: pow_succ
-/
theorem iteratedDeriv_odd_cos (n : Nat) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]

/--
theorem `differentiable_iteratedDeriv_sin` / 定理 `differentiable_iteratedDeriv_sin`

English:
theorem differentiable_iteratedDeriv_sin
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

中文:
定理 differentiable_iteratedDeriv_sin
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

Depends on / 依赖: differentiable_iteratedDeriv_sin
-/
theorem differentiable_iteratedDeriv_sin (n : Nat) :
    Differentiable Complex (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

/--
theorem `differentiable_iteratedDeriv_cos` / 定理 `differentiable_iteratedDeriv_cos`

English:
theorem differentiable_iteratedDeriv_cos
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

中文:
定理 differentiable_iteratedDeriv_cos
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

Depends on / 依赖: differentiable_iteratedDeriv_cos
-/
theorem differentiable_iteratedDeriv_cos (n : Nat) :
    Differentiable Complex (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

end Complex

namespace Real

@[simp]
/--
theorem `iteratedDeriv_add_one_sin` / 定理 `iteratedDeriv_add_one_sin`

English:
theorem iteratedDeriv_add_one_sin
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

中文:
定理 iteratedDeriv_add_one_sin
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]

Depends on / 依赖: iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_sin (n : Nat) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]

@[simp]
/--
theorem `iteratedDeriv_add_one_cos` / 定理 `iteratedDeriv_add_one_cos`

English:
theorem iteratedDeriv_add_one_cos
  given: (n : Nat)
  proof: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]

中文:
定理 iteratedDeriv_add_one_cos
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]

Depends on / 依赖: deriv.neg, iteratedDeriv_succ
-/
theorem iteratedDeriv_add_one_cos (n : Nat) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]; rw [ih]; rw [iteratedDeriv_succ]; rw [deriv.neg']
    ext x
    simp

@[simp]
/--
theorem `iteratedDeriv_even_sin` / 定理 `iteratedDeriv_even_sin`

English:
theorem iteratedDeriv_even_sin
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]

中文:
定理 iteratedDeriv_even_sin
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]

Depends on / 依赖: mul_add, pow_succ
-/
theorem iteratedDeriv_even_sin (n : Nat) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
/--
theorem `iteratedDeriv_even_cos` / 定理 `iteratedDeriv_even_cos`

English:
theorem iteratedDeriv_even_cos
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

中文:
定理 iteratedDeriv_even_cos
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

Depends on / 依赖: mul_add, pow_succ
-/
theorem iteratedDeriv_even_cos (n : Nat) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

/--
theorem `iteratedDeriv_odd_sin` / 定理 `iteratedDeriv_odd_sin`

English:
theorem iteratedDeriv_odd_sin
  given: (n : Nat)
  proof: by simp

中文:
定理 iteratedDeriv_odd_sin
  条件: (n : 自然数)
  证明: by simp
-/
theorem iteratedDeriv_odd_sin (n : Nat) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp

/--
theorem `iteratedDeriv_odd_cos` / 定理 `iteratedDeriv_odd_cos`

English:
theorem iteratedDeriv_odd_cos
  given: (n : Nat)
  proof: by simp [pow_succ]

中文:
定理 iteratedDeriv_odd_cos
  条件: (n : 自然数)
  证明: by simp [pow_succ]

Depends on / 依赖: pow_succ
-/
theorem iteratedDeriv_odd_cos (n : Nat) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]

/--
theorem `differentiable_iteratedDeriv_sin` / 定理 `differentiable_iteratedDeriv_sin`

English:
theorem differentiable_iteratedDeriv_sin
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

中文:
定理 differentiable_iteratedDeriv_sin
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

Depends on / 依赖: differentiable_iteratedDeriv_sin
-/
theorem differentiable_iteratedDeriv_sin (n : Nat) :
    Differentiable Real (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

/--
theorem `differentiable_iteratedDeriv_cos` / 定理 `differentiable_iteratedDeriv_cos`

English:
theorem differentiable_iteratedDeriv_cos
  given: (n : Nat)
  proof: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

中文:
定理 differentiable_iteratedDeriv_cos
  条件: (n : 自然数)
  证明: match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

Depends on / 依赖: differentiable_iteratedDeriv_cos
-/
theorem differentiable_iteratedDeriv_cos (n : Nat) :
    Differentiable Real (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

/--
theorem `abs_iteratedDeriv_sin_le_one` / 定理 `abs_iteratedDeriv_sin_le_one`

English:
theorem abs_iteratedDeriv_sin_le_one
  given: (n : Nat) (x : Real)
  proof: match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x

中文:
定理 abs_iteratedDeriv_sin_le_one
  条件: (n : 自然数) (x : 实数)
  证明: match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x

Depends on / 依赖: Real.abs_cos_le_one, Real.abs_sin_le_one, abs_cos_le_one, abs_iteratedDeriv_sin_le_one, abs_sin_le_one
-/
theorem abs_iteratedDeriv_sin_le_one (n : Nat) (x : Real) :
    |iteratedDeriv n sin x| <= 1 :=
  match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x

/--
theorem `abs_iteratedDeriv_cos_le_one` / 定理 `abs_iteratedDeriv_cos_le_one`

English:
theorem abs_iteratedDeriv_cos_le_one
  given: (n : Nat) (x : Real)
  proof: match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

@[simp]

中文:
定理 abs_iteratedDeriv_cos_le_one
  条件: (n : 自然数) (x : 实数)
  证明: match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

@[simp]

Depends on / 依赖: Real.abs_cos_le_one, Real.abs_sin_le_one, abs_cos_le_one, abs_iteratedDeriv_cos_le_one, abs_sin_le_one
-/
theorem abs_iteratedDeriv_cos_le_one (n : Nat) (x : Real) :
    |iteratedDeriv n cos x| <= 1 :=
  match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

@[simp]
/--
theorem `iteratedDerivWithin_sin_Icc` / 定理 `iteratedDerivWithin_sin_Icc`

English:
theorem iteratedDerivWithin_sin_Icc
  given: (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sin.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_sin_Icc
  条件: (n : 自然数) {a b : 实数} (h : a < b) {x : 实数} (hx : x in Icc a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sin.contDiffAt hx

@[simp]

Depends on / 依赖: contDiffAt, contDiff_sin, contDiff_sin.contDiffAt, homEquiv_comp, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Icc
-/
theorem iteratedDerivWithin_sin_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b) :
    iteratedDerivWithin n sin (Icc a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sin.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_cos_Icc` / 定理 `iteratedDerivWithin_cos_Icc`

English:
theorem iteratedDerivWithin_cos_Icc
  given: (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cos.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_cos_Icc
  条件: (n : 自然数) {a b : 实数} (h : a < b) {x : 实数} (hx : x in Icc a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cos.contDiffAt hx

@[simp]

Depends on / 依赖: contDiffAt, contDiff_cos, contDiff_cos.contDiffAt, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Icc
-/
theorem iteratedDerivWithin_cos_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} (hx : x in Icc a b) :
    iteratedDerivWithin n cos (Icc a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cos.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_sin_Ioo` / 定理 `iteratedDerivWithin_sin_Ioo`

English:
theorem iteratedDerivWithin_sin_Ioo
  given: (n : Nat) {a b x : Real} (hx : x in Ioo a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sin.contDiffAt hx

@[simp]

中文:
定理 iteratedDerivWithin_sin_Ioo
  条件: (n : 自然数) {a b x : 实数} (hx : x in Ioo a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sin.contDiffAt hx

@[simp]

Depends on / 依赖: contDiffAt, contDiff_sin, contDiff_sin.contDiffAt, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Ioo
-/
theorem iteratedDerivWithin_sin_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
    iteratedDerivWithin n sin (Ioo a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sin.contDiffAt hx

@[simp]
/--
theorem `iteratedDerivWithin_cos_Ioo` / 定理 `iteratedDerivWithin_cos_Ioo`

English:
theorem iteratedDerivWithin_cos_Ioo
  given: (n : Nat) {a b x : Real} (hx : x in Ioo a b)
  proof: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cos.contDiffAt hx

中文:
定理 iteratedDerivWithin_cos_Ioo
  条件: (n : 自然数) {a b x : 实数} (hx : x in Ioo a b)
  证明: iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cos.contDiffAt hx

Depends on / 依赖: contDiffAt, contDiff_cos, contDiff_cos.contDiffAt, iteratedDerivWithin_eq_iteratedDeriv, uniqueDiffOn_Ioo
-/
theorem iteratedDerivWithin_cos_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
    iteratedDerivWithin n cos (Ioo a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cos.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : Real -> Real} {f' x : Real} {s : Set Real}



/--
theorem `HasStrictDerivAt.cos` / 定理 `HasStrictDerivAt.cos`

English:
theorem HasStrictDerivAt.cos
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_cos (f x)).comp x hf

中文:
定理 HasStrictDerivAt.cos
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_cos (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_cos, hasStrictDerivAt_cos
-/
theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp x hf

/--
theorem `HasDerivAt.cos` / 定理 `HasDerivAt.cos`

English:
theorem HasDerivAt.cos
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_cos (f x)).comp x hf

中文:
定理 HasDerivAt.cos
  条件: (hf : HasDerivAt f f' x)
  证明: (Real.hasDerivAt_cos (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_cos, hasDerivAt_cos
-/
theorem HasDerivAt.cos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasDerivAt_cos (f x)).comp x hf

/--
theorem `HasDerivWithinAt.cos` / 定理 `HasDerivWithinAt.cos`

English:
theorem HasDerivWithinAt.cos
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.cos
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_cos, comp_hasDerivWithinAt, hasDerivAt_cos
-/
theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_cos` / 定理 `derivWithin_cos`

English:
theorem derivWithin_cos
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.cos.derivWithin hxs

@[simp]

中文:
定理 derivWithin_cos
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.cos.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.cos.derivWithin
-/
theorem derivWithin_cos (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cos.derivWithin hxs

@[simp]
/--
theorem `deriv_cos` / 定理 `deriv_cos`

English:
theorem deriv_cos
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.cos.deriv

中文:
定理 deriv_cos
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.cos.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.cos.deriv
-/
theorem deriv_cos (hc : DifferentiableAt Real f x) :
    deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.hasDerivAt.cos.deriv



/--
theorem `HasStrictDerivAt.sin` / 定理 `HasStrictDerivAt.sin`

English:
theorem HasStrictDerivAt.sin
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_sin (f x)).comp x hf

中文:
定理 HasStrictDerivAt.sin
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_sin (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_sin, hasStrictDerivAt_sin
-/
theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp x hf

/--
theorem `HasDerivAt.sin` / 定理 `HasDerivAt.sin`

English:
theorem HasDerivAt.sin
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_sin (f x)).comp x hf

中文:
定理 HasDerivAt.sin
  条件: (hf : HasDerivAt f f' x)
  证明: (Real.hasDerivAt_sin (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_sin, hasDerivAt_sin
-/
theorem HasDerivAt.sin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasDerivAt_sin (f x)).comp x hf

/--
theorem `HasDerivWithinAt.sin` / 定理 `HasDerivWithinAt.sin`

English:
theorem HasDerivWithinAt.sin
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.sin
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_sin, comp_hasDerivWithinAt, hasDerivAt_sin
-/
theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_sin` / 定理 `derivWithin_sin`

English:
theorem derivWithin_sin
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.sin.derivWithin hxs

@[simp]

中文:
定理 derivWithin_sin
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.sin.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.sin.derivWithin
-/
theorem derivWithin_sin (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sin.derivWithin hxs

@[simp]
/--
theorem `deriv_sin` / 定理 `deriv_sin`

English:
theorem deriv_sin
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.sin.deriv

中文:
定理 deriv_sin
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.sin.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.sin.deriv
-/
theorem deriv_sin (hc : DifferentiableAt Real f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.hasDerivAt.sin.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {f' : StrongDual Real E}
  {x : E} {s : Set E}



/--
theorem `HasStrictFDerivAt.cos` / 定理 `HasStrictFDerivAt.cos`

English:
theorem HasStrictFDerivAt.cos
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.cos
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Real.hasStrictDerivAt_cos, comp_hasStrictFDerivAt, hasStrictDerivAt_cos
-/
theorem HasStrictFDerivAt.cos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.cos` / 定理 `HasFDerivAt.cos`

English:
theorem HasFDerivAt.cos
  given: (hf : HasFDerivAt f f' x)
  proof: (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

中文:
定理 HasFDerivAt.cos
  条件: (hf : HasFDerivAt f f' x)
  证明: (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Real.hasDerivAt_cos, comp_hasFDerivAt, hasDerivAt_cos
-/
theorem HasFDerivAt.cos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.cos` / 定理 `HasFDerivWithinAt.cos`

English:
theorem HasFDerivWithinAt.cos
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.cos
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_cos, comp_hasFDerivWithinAt, hasDerivAt_cos
-/
theorem HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.cos` / 定理 `DifferentiableWithinAt.cos`

English:
theorem DifferentiableWithinAt.cos
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.cos.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.cos
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.cos.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.cos.differentiableWithinAt
-/
theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.cos (f x)) s x :=
  hf.hasFDerivWithinAt.cos.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.cos` / 定理 `DifferentiableAt.cos`

English:
theorem DifferentiableAt.cos
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.cos.differentiableAt

中文:
定理 DifferentiableAt.cos
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.cos.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.cos.differentiableAt
-/
theorem DifferentiableAt.cos (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => Real.cos (f x)) x :=
  hc.hasFDerivAt.cos.differentiableAt

/--
theorem `DifferentiableOn.cos` / 定理 `DifferentiableOn.cos`

English:
theorem DifferentiableOn.cos
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).cos

@[simp, fun_prop]

中文:
定理 DifferentiableOn.cos
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).cos

@[simp, fun_prop]
-/
theorem DifferentiableOn.cos (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => Real.cos (f x)) s := fun x h => (hc x h).cos

@[simp, fun_prop]
/--
theorem `Differentiable.cos` / 定理 `Differentiable.cos`

English:
theorem Differentiable.cos
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => Real.cos (f x)
  proof: fun x => (hc x).cos

中文:
定理 Differentiable.cos
  条件: (hc : Differentiable 实数 f)
  结论: Differentiable 实数 fun x => 实数.cos (f x)
  证明: fun x => (hc x).cos
-/
theorem Differentiable.cos (hc : Differentiable Real f) : Differentiable Real fun x => Real.cos (f x) :=
  fun x => (hc x).cos

/--
theorem `fderivWithin_cos` / 定理 `fderivWithin_cos`

English:
theorem fderivWithin_cos
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.cos.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_cos
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.cos.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.cos.fderivWithin
-/
theorem fderivWithin_cos (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.cos.fderivWithin hxs

@[simp]
/--
theorem `fderiv_cos` / 定理 `fderiv_cos`

English:
theorem fderiv_cos
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.cos.fderiv

中文:
定理 fderiv_cos
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.cos.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.cos.fderiv
-/
theorem fderiv_cos (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv Real f x :=
  hc.hasFDerivAt.cos.fderiv

/--
theorem `ContDiff.cos` / 定理 `ContDiff.cos`

English:
theorem ContDiff.cos
  given: {n} (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => Real.cos (f x)
  proof: Real.contDiff_cos.comp h

中文:
定理 ContDiff.cos
  条件: {n} (h : ContDiff 实数 n f)
  结论: ContDiff 实数 n fun x => 实数.cos (f x)
  证明: Real.contDiff_cos.comp h

Depends on / 依赖: Real.contDiff_cos.comp, contDiff_cos
-/
theorem ContDiff.cos {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.cos (f x) :=
  Real.contDiff_cos.comp h

/--
theorem `ContDiffAt.cos` / 定理 `ContDiffAt.cos`

English:
theorem ContDiffAt.cos
  given: {n} (hf : ContDiffAt Real n f x)
  statement: ContDiffAt Real n (fun x => Real.cos (f x)) x
  proof: Real.contDiff_cos.contDiffAt.comp x hf

中文:
定理 ContDiffAt.cos
  条件: {n} (hf : ContDiffAt 实数 n f x)
  结论: ContDiffAt 实数 n (fun x => 实数.cos (f x)) x
  证明: Real.contDiff_cos.contDiffAt.comp x hf

Depends on / 依赖: Real.contDiff_cos.contDiffAt.comp, contDiffAt, contDiff_cos
-/
theorem ContDiffAt.cos {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x => Real.cos (f x)) x :=
  Real.contDiff_cos.contDiffAt.comp x hf

/--
theorem `ContDiffOn.cos` / 定理 `ContDiffOn.cos`

English:
theorem ContDiffOn.cos
  given: {n} (hf : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun x => Real.cos (f x)) s
  proof: Real.contDiff_cos.comp_contDiffOn hf

中文:
定理 ContDiffOn.cos
  条件: {n} (hf : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun x => 实数.cos (f x)) s
  证明: Real.contDiff_cos.comp_contDiffOn hf

Depends on / 依赖: Real.contDiff_cos.comp_contDiffOn, comp_contDiffOn, contDiff_cos
-/
theorem ContDiffOn.cos {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x => Real.cos (f x)) s :=
  Real.contDiff_cos.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.cos` / 定理 `ContDiffWithinAt.cos`

English:
theorem ContDiffWithinAt.cos
  given: {n} (hf : ContDiffWithinAt Real n f s x)
  proof: Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.cos
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x)
  证明: Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_cos
-/
theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => Real.cos (f x)) s x :=
  Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf



/--
theorem `HasStrictFDerivAt.sin` / 定理 `HasStrictFDerivAt.sin`

English:
theorem HasStrictFDerivAt.sin
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.sin
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Real.hasStrictDerivAt_sin, comp_hasStrictFDerivAt, hasStrictDerivAt_sin
-/
theorem HasStrictFDerivAt.sin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.sin` / 定理 `HasFDerivAt.sin`

English:
theorem HasFDerivAt.sin
  given: (hf : HasFDerivAt f f' x)
  proof: (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

中文:
定理 HasFDerivAt.sin
  条件: (hf : HasFDerivAt f f' x)
  证明: (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Real.hasDerivAt_sin, comp_hasFDerivAt, hasDerivAt_sin
-/
theorem HasFDerivAt.sin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.sin` / 定理 `HasFDerivWithinAt.sin`

English:
theorem HasFDerivWithinAt.sin
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.sin
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_sin, comp_hasFDerivWithinAt, decidableEq, discreteEquiv, discreteEquiv.decidableEq, hasDerivAt_sin
-/
theorem HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `DifferentiableWithinAt.sin` / 定理 `DifferentiableWithinAt.sin`

English:
theorem DifferentiableWithinAt.sin
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.sin.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.sin
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.sin.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.sin.differentiableWithinAt
-/
theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.sin (f x)) s x :=
  hf.hasFDerivWithinAt.sin.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.sin` / 定理 `DifferentiableAt.sin`

English:
theorem DifferentiableAt.sin
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.sin.differentiableAt

中文:
定理 DifferentiableAt.sin
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.sin.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.sin.differentiableAt
-/
theorem DifferentiableAt.sin (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => Real.sin (f x)) x :=
  hc.hasFDerivAt.sin.differentiableAt

/--
theorem `DifferentiableOn.sin` / 定理 `DifferentiableOn.sin`

English:
theorem DifferentiableOn.sin
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).sin

@[simp, fun_prop]

中文:
定理 DifferentiableOn.sin
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).sin

@[simp, fun_prop]
-/
theorem DifferentiableOn.sin (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => Real.sin (f x)) s := fun x h => (hc x h).sin

@[simp, fun_prop]
/--
theorem `Differentiable.sin` / 定理 `Differentiable.sin`

English:
theorem Differentiable.sin
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => Real.sin (f x)
  proof: fun x => (hc x).sin

中文:
定理 Differentiable.sin
  条件: (hc : Differentiable 实数 f)
  结论: Differentiable 实数 fun x => 实数.sin (f x)
  证明: fun x => (hc x).sin
-/
theorem Differentiable.sin (hc : Differentiable Real f) : Differentiable Real fun x => Real.sin (f x) :=
  fun x => (hc x).sin

/--
theorem `fderivWithin_sin` / 定理 `fderivWithin_sin`

English:
theorem fderivWithin_sin
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.sin.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_sin
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.sin.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.sin.fderivWithin
-/
theorem fderivWithin_sin (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.sin.fderivWithin hxs

@[simp]
/--
theorem `fderiv_sin` / 定理 `fderiv_sin`

English:
theorem fderiv_sin
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.sin.fderiv

中文:
定理 fderiv_sin
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.sin.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.sin.fderiv
-/
theorem fderiv_sin (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv Real f x :=
  hc.hasFDerivAt.sin.fderiv

/--
theorem `ContDiff.sin` / 定理 `ContDiff.sin`

English:
theorem ContDiff.sin
  given: {n} (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => Real.sin (f x)
  proof: Real.contDiff_sin.comp h

中文:
定理 ContDiff.sin
  条件: {n} (h : ContDiff 实数 n f)
  结论: ContDiff 实数 n fun x => 实数.sin (f x)
  证明: Real.contDiff_sin.comp h

Depends on / 依赖: Real.contDiff_sin.comp, contDiff_sin
-/
theorem ContDiff.sin {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.sin (f x) :=
  Real.contDiff_sin.comp h

/--
theorem `ContDiffAt.sin` / 定理 `ContDiffAt.sin`

English:
theorem ContDiffAt.sin
  given: {n} (hf : ContDiffAt Real n f x)
  statement: ContDiffAt Real n (fun x => Real.sin (f x)) x
  proof: Real.contDiff_sin.contDiffAt.comp x hf

中文:
定理 ContDiffAt.sin
  条件: {n} (hf : ContDiffAt 实数 n f x)
  结论: ContDiffAt 实数 n (fun x => 实数.sin (f x)) x
  证明: Real.contDiff_sin.contDiffAt.comp x hf

Depends on / 依赖: Real.contDiff_sin.contDiffAt.comp, contDiffAt, contDiff_sin
-/
theorem ContDiffAt.sin {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x => Real.sin (f x)) x :=
  Real.contDiff_sin.contDiffAt.comp x hf

/--
theorem `ContDiffOn.sin` / 定理 `ContDiffOn.sin`

English:
theorem ContDiffOn.sin
  given: {n} (hf : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun x => Real.sin (f x)) s
  proof: Real.contDiff_sin.comp_contDiffOn hf

中文:
定理 ContDiffOn.sin
  条件: {n} (hf : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun x => 实数.sin (f x)) s
  证明: Real.contDiff_sin.comp_contDiffOn hf

Depends on / 依赖: Real.contDiff_sin.comp_contDiffOn, comp_contDiffOn, contDiff_sin
-/
theorem ContDiffOn.sin {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x => Real.sin (f x)) s :=
  Real.contDiff_sin.comp_contDiffOn hf

/--
theorem `ContDiffWithinAt.sin` / 定理 `ContDiffWithinAt.sin`

English:
theorem ContDiffWithinAt.sin
  given: {n} (hf : ContDiffWithinAt Real n f s x)
  proof: Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.sin
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x)
  证明: Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_sin
-/
theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => Real.sin (f x)) s x :=
  Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

@[simp]
/--
theorem `Complex.logDeriv_sin` / 定理 `Complex.logDeriv_sin`

English:
theorem Complex.logDeriv_sin
  statement: logDeriv (Complex.sin) = Complex.cot
  proof: by
  ext
  rw [logDeriv]; rw [Complex.deriv_sin]; rw [Pi.div_apply]; rw [Complex.cot]

@[simp]

中文:
定理 Complex.logDeriv_sin
  结论: logDeriv (Complex.sin) = Complex.cot
  证明: by
  ext
  rw [logDeriv]; rw [Complex.deriv_sin]; rw [Pi.div_apply]; rw [Complex.cot]

@[simp]

Depends on / 依赖: Complex.cot, Complex.deriv_sin, Discrete, Discrete.eqToHom, Pi.div_apply, cat_disch, deriv_sin, div_apply, eqToHom, eq_of_hom, logDeriv
-/
theorem Complex.logDeriv_sin : logDeriv (Complex.sin) = Complex.cot := by
  ext
  rw [logDeriv]; rw [Complex.deriv_sin]; rw [Pi.div_apply]; rw [Complex.cot]

@[simp]
/--
theorem `Real.logDeriv_sin` / 定理 `Real.logDeriv_sin`

English:
theorem Real.logDeriv_sin
  statement: logDeriv (Real.sin) = Real.cot
  proof: by
  ext
  rw [logDeriv]; rw [Real.deriv_sin]; rw [Pi.div_apply]; rw [Real.cot_eq_cos_div_sin]

@[simp]

中文:
定理 Real.logDeriv_sin
  结论: logDeriv (实数.sin) = 实数.cot
  证明: by
  ext
  rw [logDeriv]; rw [Real.deriv_sin]; rw [Pi.div_apply]; rw [Real.cot_eq_cos_div_sin]

@[simp]

Depends on / 依赖: Pi.div_apply, Real.cot_eq_cos_div_sin, Real.deriv_sin, cot_eq_cos_div_sin, deriv_sin, div_apply, logDeriv
-/
theorem Real.logDeriv_sin : logDeriv (Real.sin) = Real.cot := by
  ext
  rw [logDeriv]; rw [Real.deriv_sin]; rw [Pi.div_apply]; rw [Real.cot_eq_cos_div_sin]

@[simp]
/--
theorem `Complex.logDeriv_cos` / 定理 `Complex.logDeriv_cos`

English:
theorem Complex.logDeriv_cos
  statement: logDeriv (Complex.cos) = -Complex.tan
  proof: by
  ext
  rw [logDeriv]; rw [Complex.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [Complex.tan]; rw [neg_div]

@[simp]

中文:
定理 Complex.logDeriv_cos
  结论: logDeriv (Complex.cos) = -Complex.tan
  证明: by
  ext
  rw [logDeriv]; rw [Complex.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [Complex.tan]; rw [neg_div]

@[simp]

Depends on / 依赖: Complex.deriv_cos, Complex.tan, Pi.div_apply, Pi.neg_apply, deriv_cos, div_apply, logDeriv, neg_apply, neg_div
-/
theorem Complex.logDeriv_cos : logDeriv (Complex.cos) = -Complex.tan := by
  ext
  rw [logDeriv]; rw [Complex.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [Complex.tan]; rw [neg_div]

@[simp]
/--
theorem `Real.logDeriv_cos` / 定理 `Real.logDeriv_cos`

English:
theorem Real.logDeriv_cos
  statement: logDeriv (Real.cos) = -Real.tan
  proof: by
  ext
  rw [logDeriv]; rw [Real.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [neg_div]; rw [Real.tan_eq_sin_div_cos]

@[simp]

中文:
定理 Real.logDeriv_cos
  结论: logDeriv (实数.cos) = -实数.tan
  证明: by
  ext
  rw [logDeriv]; rw [Real.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [neg_div]; rw [Real.tan_eq_sin_div_cos]

@[simp]

Depends on / 依赖: Pi.div_apply, Pi.neg_apply, Real.deriv_cos, Real.tan_eq_sin_div_cos, deriv_cos, div_apply, logDeriv, neg_apply, neg_div, tan_eq_sin_div_cos
-/
theorem Real.logDeriv_cos : logDeriv (Real.cos) = -Real.tan := by
  ext
  rw [logDeriv]; rw [Real.deriv_cos']; rw [Pi.div_apply]; rw [Pi.neg_apply]; rw [neg_div]; rw [Real.tan_eq_sin_div_cos]

@[simp]
/--
theorem `Complex.logDeriv_exp` / 定理 `Complex.logDeriv_exp`

English:
theorem Complex.logDeriv_exp
  statement: logDeriv (Complex.exp) = 1
  proof: by
  ext
  rw [logDeriv]; rw [Complex.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Complex.LogDeriv_exp := Complex.logDeriv_exp

@[simp]

中文:
定理 Complex.logDeriv_exp
  结论: logDeriv (Complex.exp) = 1
  证明: by
  ext
  rw [logDeriv]; rw [Complex.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Complex.LogDeriv_exp := Complex.logDeriv_exp

@[simp]

Depends on / 依赖: Complex.deriv_exp, Pi.div_apply, Pi.one_apply, deriv_exp, div_apply, exp_sub, exp_zero, logDeriv, one_apply, sub_self
-/
theorem Complex.logDeriv_exp : logDeriv (Complex.exp) = 1 := by
  ext
  rw [logDeriv]; rw [Complex.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Complex.LogDeriv_exp := Complex.logDeriv_exp

@[simp]
/--
theorem `Real.logDeriv_exp` / 定理 `Real.logDeriv_exp`

English:
theorem Real.logDeriv_exp
  statement: logDeriv (Real.exp) = 1
  proof: by
  ext
  rw [logDeriv]; rw [Real.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Real.LogDeriv_exp := Real.logDeriv_exp

中文:
定理 Real.logDeriv_exp
  结论: logDeriv (实数.exp) = 1
  证明: by
  ext
  rw [logDeriv]; rw [Real.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Real.LogDeriv_exp := Real.logDeriv_exp

Depends on / 依赖: Pi.div_apply, Pi.one_apply, Real.deriv_exp, deriv_exp, div_apply, exp_sub, exp_zero, logDeriv, one_apply, sub_self
-/
theorem Real.logDeriv_exp : logDeriv (Real.exp) = 1 := by
  ext
  rw [logDeriv]; rw [Real.deriv_exp]; rw [Pi.div_apply]; rw [← exp_sub]; rw [sub_self]; rw [exp_zero]; rw [Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Real.LogDeriv_exp := Real.logDeriv_exp

end LogDeriv

end
