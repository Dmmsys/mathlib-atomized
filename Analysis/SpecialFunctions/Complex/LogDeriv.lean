/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of the complex `log` function

-/

public section

assert_not_exists IsConformalMap Conformal

open Set Filter

open scoped Real Topology

namespace Complex

/--
theorem `isOpenMap_exp` / 定理 `isOpenMap_exp`

English:
theorem isOpenMap_exp
  statement: IsOpenMap exp
  proof: isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero

中文:
定理 isOpenMap_exp
  结论: IsOpenMap exp
  证明: isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero

Depends on / 依赖: exp_ne_zero, hasStrictDerivAt_exp, isOpenMap_of_hasStrictDerivAt
-/
theorem isOpenMap_exp : IsOpenMap exp :=
  isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero

/--
theorem `hasStrictDerivAt_log` / 定理 `hasStrictDerivAt_log`

English:
theorem hasStrictDerivAt_log
  given: {x : Complex} (h : x in slitPlane)
  statement: HasStrictDerivAt log x⁻¹ x
  proof: have h0 : x != 0 := slitPlane_ne_zero h
expOpenPartialHomeomorph.hasStrictDerivAt_symm h h0 by
    simpa [exp_log h0] using! hasStrictDerivAt_exp (log x)

中文:
定理 hasStrictDerivAt_log
  条件: {x : Complex} (h : x in slitPlane)
  结论: HasStrictDerivAt log x⁻¹ x
  证明: have h0 : x != 0 := slitPlane_ne_zero h
expOpenPartialHomeomorph.hasStrictDerivAt_symm h h0 by
    simpa [exp_log h0] using! hasStrictDerivAt_exp (log x)

Depends on / 依赖: expOpenPartialHomeomorph, expOpenPartialHomeomorph.hasStrictDerivAt_symm, exp_log, hasStrictDerivAt_exp, hasStrictDerivAt_symm, slitPlane_ne_zero
-/
theorem hasStrictDerivAt_log {x : Complex} (h : x in slitPlane) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x != 0 := slitPlane_ne_zero h
expOpenPartialHomeomorph.hasStrictDerivAt_symm h h0 by
    simpa [exp_log h0] using! hasStrictDerivAt_exp (log x)

/--
lemma `hasDerivAt_log` / 引理 `hasDerivAt_log`

English:
lemma hasDerivAt_log
  given: {z : Complex} (hz : z in slitPlane)
  statement: HasDerivAt log z⁻¹ z
  proof: HasStrictDerivAt.hasDerivAt hasStrictDerivAt_log hz

@[fun_prop]

中文:
引理 hasDerivAt_log
  条件: {z : Complex} (hz : z in slitPlane)
  结论: HasDerivAt log z⁻¹ z
  证明: HasStrictDerivAt.hasDerivAt hasStrictDerivAt_log hz

@[fun_prop]

Depends on / 依赖: HasStrictDerivAt, HasStrictDerivAt.hasDerivAt, hasDerivAt, hasStrictDerivAt_log
-/
lemma hasDerivAt_log {z : Complex} (hz : z in slitPlane) : HasDerivAt log z⁻¹ z :=
HasStrictDerivAt.hasDerivAt hasStrictDerivAt_log hz

@[fun_prop]
/--
lemma `differentiableAt_log` / 引理 `differentiableAt_log`

English:
lemma differentiableAt_log
  given: {z : Complex} (hz : z in slitPlane)
  statement: DifferentiableAt Complex log z
  proof: (hasDerivAt_log hz).differentiableAt

@[fun_prop]

中文:
引理 differentiableAt_log
  条件: {z : Complex} (hz : z in slitPlane)
  结论: DifferentiableAt Complex log z
  证明: (hasDerivAt_log hz).differentiableAt

@[fun_prop]

Depends on / 依赖: HasExactColimitsOfShape, HasExactColimitsOfShape.domain_of_functor, Ind.inclusion, differentiableAt, domain_of_functor, hasDerivAt_log, inclusion
-/
lemma differentiableAt_log {z : Complex} (hz : z in slitPlane) : DifferentiableAt Complex log z :=
  (hasDerivAt_log hz).differentiableAt

@[fun_prop]
/--
theorem `hasStrictFDerivAt_log_real` / 定理 `hasStrictFDerivAt_log_real`

English:
theorem hasStrictFDerivAt_log_real
  given: {x : Complex} (h : x in slitPlane)
  proof: (hasStrictDerivAt_log h).complexToReal_fderiv

中文:
定理 hasStrictFDerivAt_log_real
  条件: {x : Complex} (h : x in slitPlane)
  证明: (hasStrictDerivAt_log h).complexToReal_fderiv

Depends on / 依赖: complexToReal_fderiv, hasStrictDerivAt_log
-/
theorem hasStrictFDerivAt_log_real {x : Complex} (h : x in slitPlane) :
    HasStrictFDerivAt log (x⁻¹ • (1 : Complex ->L[Real] Complex)) x :=
  (hasStrictDerivAt_log h).complexToReal_fderiv

/--
theorem `contDiffAt_log` / 定理 `contDiffAt_log`

English:
theorem contDiffAt_log
  given: {x : Complex} (h : x in slitPlane) {n : WithTop Nat∞}
  statement: ContDiffAt Complex n log x
  proof: expOpenPartialHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt

中文:
定理 contDiffAt_log
  条件: {x : Complex} (h : x in slitPlane) {n : WithTop 自然数∞}
  结论: ContDiffAt Complex n log x
  证明: expOpenPartialHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt

Depends on / 依赖: contDiffAt, contDiffAt_symm_deriv, contDiff_exp, contDiff_exp.contDiffAt, expOpenPartialHomeomorph, expOpenPartialHomeomorph.contDiffAt_symm_deriv, exp_ne_zero, hasDerivAt_exp
-/
theorem contDiffAt_log {x : Complex} (h : x in slitPlane) {n : WithTop Nat∞} : ContDiffAt Complex n log x :=
  expOpenPartialHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt

/--
theorem `deriv_log` / 定理 `deriv_log`

English:
theorem deriv_log
  given: {x : Complex} (h : x in slitPlane)
  statement: deriv log x = x⁻¹
  proof: (hasDerivAt_log h).deriv

中文:
定理 deriv_log
  条件: {x : Complex} (h : x in slitPlane)
  结论: deriv log x = x⁻¹
  证明: (hasDerivAt_log h).deriv

Depends on / 依赖: hasDerivAt_log
-/
theorem deriv_log {x : Complex} (h : x in slitPlane) : deriv log x = x⁻¹ :=
  (hasDerivAt_log h).deriv

end Complex

section LogDeriv

open Complex Filter

open scoped Topology

variable {α : Type*} [TopologicalSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
theorem `HasStrictFDerivAt.clog` / 定理 `HasStrictFDerivAt.clog`

English:
theorem HasStrictFDerivAt.clog
  statement: {f : E -> Complex} {f' : StrongDual Complex E} {x : E}
  proof: (hasStrictDerivAt_log h₂).comp_hasStrictFDerivAt x h₁

中文:
定理 HasStrictFDerivAt.clog
  结论: {f : E -> Complex} {f' : StrongDual Complex E} {x : E}
  证明: (hasStrictDerivAt_log h₂).comp_hasStrictFDerivAt x h₁

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_log
-/
theorem HasStrictFDerivAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {x : E}
    (h₁ : HasStrictFDerivAt f f' x) (h₂ : f x in slitPlane) :
    HasStrictFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).comp_hasStrictFDerivAt x h₁

/--
theorem `HasStrictDerivAt.clog` / 定理 `HasStrictDerivAt.clog`

English:
theorem HasStrictDerivAt.clog
  statement: {f : Complex -> Complex} {f' x : Complex} (h₁ : HasStrictDerivAt f f' x)
  proof: by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).comp x h₁

中文:
定理 HasStrictDerivAt.clog
  结论: {f : Complex -> Complex} {f' x : Complex} (h₁ : HasStrictDerivAt f f' x)
  证明: by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).comp x h₁

Depends on / 依赖: div_eq_inv_mul, hasStrictDerivAt_log
-/
theorem HasStrictDerivAt.clog {f : Complex -> Complex} {f' x : Complex} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x in slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).comp x h₁

/--
theorem `HasStrictDerivAt.clog_real` / 定理 `HasStrictDerivAt.clog_real`

English:
theorem HasStrictDerivAt.clog_real
  statement: {f : Real -> Complex} {x : Real} {f' : Complex} (h₁ : HasStrictDerivAt f f' x)
  proof: by
  simpa only [div_eq_inv_mul] using! (hasStrictFDerivAt_log_real h₂).comp_hasStrictDerivAt x h₁

中文:
定理 HasStrictDerivAt.clog_real
  结论: {f : 实数 -> Complex} {x : 实数} {f' : Complex} (h₁ : HasStrictDerivAt f f' x)
  证明: by
  simpa only [div_eq_inv_mul] using! (hasStrictFDerivAt_log_real h₂).comp_hasStrictDerivAt x h₁

Depends on / 依赖: comp_hasStrictDerivAt, div_eq_inv_mul, hasStrictFDerivAt_log_real
-/
theorem HasStrictDerivAt.clog_real {f : Real -> Complex} {x : Real} {f' : Complex} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x in slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using! (hasStrictFDerivAt_log_real h₂).comp_hasStrictDerivAt x h₁

/--
theorem `HasFDerivAt.clog` / 定理 `HasFDerivAt.clog`

English:
theorem HasFDerivAt.clog
  statement: {f : E -> Complex} {f' : StrongDual Complex E} {x : E} (h₁ : HasFDerivAt f f' x)
  proof: (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivAt x h₁

中文:
定理 HasFDerivAt.clog
  结论: {f : E -> Complex} {f' : StrongDual Complex E} {x : E} (h₁ : HasFDerivAt f f' x)
  证明: (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivAt x h₁

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt, hasDerivAt.comp_hasFDerivAt, hasStrictDerivAt_log
-/
theorem HasFDerivAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {x : E} (h₁ : HasFDerivAt f f' x)
    (h₂ : f x in slitPlane) : HasFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivAt x h₁

/--
theorem `HasDerivAt.clog` / 定理 `HasDerivAt.clog`

English:
theorem HasDerivAt.clog
  statement: {f : Complex -> Complex} {f' x : Complex} (h₁ : HasDerivAt f f' x)
  proof: by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁

中文:
定理 HasDerivAt.clog
  结论: {f : Complex -> Complex} {f' x : Complex} (h₁ : HasDerivAt f f' x)
  证明: by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁

Depends on / 依赖: div_eq_inv_mul, hasDerivAt, hasDerivAt.comp, hasStrictDerivAt_log
-/
theorem HasDerivAt.clog {f : Complex -> Complex} {f' x : Complex} (h₁ : HasDerivAt f f' x)
    (h₂ : f x in slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁

/--
theorem `HasDerivAt.clog_real` / 定理 `HasDerivAt.clog_real`

English:
theorem HasDerivAt.clog_real
  statement: {f : Real -> Complex} {x : Real} {f' : Complex} (h₁ : HasDerivAt f f' x)
  proof: by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivAt x h₁

中文:
定理 HasDerivAt.clog_real
  结论: {f : 实数 -> Complex} {x : 实数} {f' : Complex} (h₁ : HasDerivAt f f' x)
  证明: by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivAt x h₁

Depends on / 依赖: comp_hasDerivAt, div_eq_inv_mul, hasFDerivAt, hasFDerivAt.comp_hasDerivAt, hasStrictFDerivAt_log_real
-/
theorem HasDerivAt.clog_real {f : Real -> Complex} {x : Real} {f' : Complex} (h₁ : HasDerivAt f f' x)
    (h₂ : f x in slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivAt x h₁

/--
theorem `DifferentiableAt.clog` / 定理 `DifferentiableAt.clog`

English:
theorem DifferentiableAt.clog
  statement: {f : E -> Complex} {x : E} (h₁ : DifferentiableAt Complex f x)
  proof: (h₁.hasFDerivAt.clog h₂).differentiableAt

中文:
定理 DifferentiableAt.clog
  结论: {f : E -> Complex} {x : E} (h₁ : DifferentiableAt Complex f x)
  证明: (h₁.hasFDerivAt.clog h₂).differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hasFDerivAt.clog
-/
theorem DifferentiableAt.clog {f : E -> Complex} {x : E} (h₁ : DifferentiableAt Complex f x)
    (h₂ : f x in slitPlane) : DifferentiableAt Complex (fun t => log (f t)) x :=
  (h₁.hasFDerivAt.clog h₂).differentiableAt

/--
theorem `HasFDerivWithinAt.clog` / 定理 `HasFDerivWithinAt.clog`

English:
theorem HasFDerivWithinAt.clog
  statement: {f : E -> Complex} {f' : StrongDual Complex E} {s : Set E} {x : E}
  proof: (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁

中文:
定理 HasFDerivWithinAt.clog
  结论: {f : E -> Complex} {f' : StrongDual Complex E} {s : Set E} {x : E}
  证明: (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt, hasDerivAt.comp_hasFDerivWithinAt, hasStrictDerivAt_log
-/
theorem HasFDerivWithinAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {s : Set E} {x : E}
    (h₁ : HasFDerivWithinAt f f' s x) (h₂ : f x in slitPlane) :
    HasFDerivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁

/--
theorem `HasDerivWithinAt.clog` / 定理 `HasDerivWithinAt.clog`

English:
theorem HasDerivWithinAt.clog
  statement: {f : Complex -> Complex} {f' x : Complex} {s : Set Complex} (h₁ : HasDerivWithinAt f f' s x)
  proof: by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁

中文:
定理 HasDerivWithinAt.clog
  结论: {f : Complex -> Complex} {f' x : Complex} {s : Set Complex} (h₁ : HasDerivWithinAt f f' s x)
  证明: by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁

Depends on / 依赖: comp_hasDerivWithinAt, div_eq_inv_mul, hasDerivAt, hasDerivAt.comp_hasDerivWithinAt, hasStrictDerivAt_log
-/
theorem HasDerivWithinAt.clog {f : Complex -> Complex} {f' x : Complex} {s : Set Complex} (h₁ : HasDerivWithinAt f f' s x)
    (h₂ : f x in slitPlane) : HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁

/--
theorem `HasDerivWithinAt.clog_real` / 定理 `HasDerivWithinAt.clog_real`

English:
theorem HasDerivWithinAt.clog_real
  statement: {f : Real -> Complex} {s : Set Real} {x : Real} {f' : Complex}
  proof: by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivWithinAt x h₁

中文:
定理 HasDerivWithinAt.clog_real
  结论: {f : 实数 -> Complex} {s : Set 实数} {x : 实数} {f' : Complex}
  证明: by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivWithinAt x h₁

Depends on / 依赖: comp_hasDerivWithinAt, div_eq_inv_mul, hasFDerivAt, hasFDerivAt.comp_hasDerivWithinAt, hasStrictFDerivAt_log_real
-/
theorem HasDerivWithinAt.clog_real {f : Real -> Complex} {s : Set Real} {x : Real} {f' : Complex}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x in slitPlane) :
    HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivWithinAt x h₁

/--
theorem `DifferentiableWithinAt.clog` / 定理 `DifferentiableWithinAt.clog`

English:
theorem DifferentiableWithinAt.clog
  statement: {f : E -> Complex} {s : Set E} {x : E}
  proof: (h₁.hasFDerivWithinAt.clog h₂).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.clog
  结论: {f : E -> Complex} {s : Set E} {x : E}
  证明: (h₁.hasFDerivWithinAt.clog h₂).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hasFDerivWithinAt.clog
-/
theorem DifferentiableWithinAt.clog {f : E -> Complex} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt Complex f s x) (h₂ : f x in slitPlane) :
    DifferentiableWithinAt Complex (fun t => log (f t)) s x :=
  (h₁.hasFDerivWithinAt.clog h₂).differentiableWithinAt

/--
theorem `DifferentiableOn.clog` / 定理 `DifferentiableOn.clog`

English:
theorem DifferentiableOn.clog
  statement: {f : E -> Complex} {s : Set E} (h₁ : DifferentiableOn Complex f s)
  proof: fun x hx => (h₁ x hx).clog (h₂ x hx)

中文:
定理 DifferentiableOn.clog
  结论: {f : E -> Complex} {s : Set E} (h₁ : DifferentiableOn Complex f s)
  证明: fun x hx => (h₁ x hx).clog (h₂ x hx)
-/
theorem DifferentiableOn.clog {f : E -> Complex} {s : Set E} (h₁ : DifferentiableOn Complex f s)
    (h₂ : forall x in s, f x in slitPlane) : DifferentiableOn Complex (fun t => log (f t)) s :=
  fun x hx => (h₁ x hx).clog (h₂ x hx)

/--
theorem `Differentiable.clog` / 定理 `Differentiable.clog`

English:
theorem Differentiable.clog
  statement: {f : E -> Complex} (h₁ : Differentiable Complex f)
  proof: fun x =>
  (h₁ x).clog (h₂ x)

中文:
定理 Differentiable.clog
  结论: {f : E -> Complex} (h₁ : Differentiable Complex f)
  证明: fun x =>
  (h₁ x).clog (h₂ x)
-/
theorem Differentiable.clog {f : E -> Complex} (h₁ : Differentiable Complex f)
    (h₂ : forall x, f x in slitPlane) : Differentiable Complex fun t => log (f t) := fun x =>
  (h₁ x).clog (h₂ x)

/--
lemma `Complex.deriv_log_comp_eq_logDeriv` / 引理 `Complex.deriv_log_comp_eq_logDeriv`

English:
lemma Complex.deriv_log_comp_eq_logDeriv
  statement: {f : Complex -> Complex} {x : Complex} (h₁ : DifferentiableAt Complex f x)
  proof: by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

中文:
引理 Complex.deriv_log_comp_eq_logDeriv
  结论: {f : Complex -> Complex} {x : Complex} (h₁ : DifferentiableAt Complex f x)
  证明: by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, HasDerivAt.clog, Pi.div_apply, comp_def, div_apply, hasDerivAt, hasDerivAt.deriv, logDeriv
-/
lemma Complex.deriv_log_comp_eq_logDeriv {f : Complex -> Complex} {x : Complex} (h₁ : DifferentiableAt Complex f x)
    (h₂ : f x in Complex.slitPlane) : deriv (Complex.log ∘ f) x = logDeriv f x := by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

end LogDeriv
