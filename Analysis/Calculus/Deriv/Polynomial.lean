/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/

public section


universe u

open scoped Polynomial

open ContinuousLinearMap (smulRight)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {R : Type*} [CommSemiring R] [Algebra R 𝕜]
variable (p : 𝕜[X]) (q : R[X])

/--
theorem `hasStrictDerivAt` / 定理 `hasStrictDerivAt`

English:
theorem hasStrictDerivAt
  given: (x : 𝕜)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using! hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using! (hasStrictDerivAt_pow n x).const_mul a

中文:
定理 hasStrictDerivAt
  条件: (x : 𝕜)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using! hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using! (hasStrictDerivAt_pow n x).const_mul a
-/
protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using! hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using! (hasStrictDerivAt_pow n x).const_mul a

/--
theorem `hasStrictDerivAt_aeval` / 定理 `hasStrictDerivAt_aeval`

English:
theorem hasStrictDerivAt_aeval
  given: (x : 𝕜)
  proof: by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x

中文:
定理 hasStrictDerivAt_aeval
  条件: (x : 𝕜)
  证明: by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x
-/
protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x

/--
theorem `hasDerivAt` / 定理 `hasDerivAt`

English:
theorem hasDerivAt
  given: (x : 𝕜)
  statement: HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x
  proof: (p.hasStrictDerivAt x).hasDerivAt

中文:
定理 hasDerivAt
  条件: (x : 𝕜)
  结论: 在点处可导 (fun x => p.eval x) (p.derivative.eval x) x
  证明: (p.hasStrictDerivAt x).hasDerivAt
-/
protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt

/--
theorem `hasDerivAt_aeval` / 定理 `hasDerivAt_aeval`

English:
theorem hasDerivAt_aeval
  given: (x : 𝕜)
  proof: (q.hasStrictDerivAt_aeval x).hasDerivAt

中文:
定理 hasDerivAt_aeval
  条件: (x : 𝕜)
  证明: (q.hasStrictDerivAt_aeval x).hasDerivAt
-/
protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt

/--
theorem `hasDerivWithinAt` / 定理 `hasDerivWithinAt`

English:
theorem hasDerivWithinAt
  given: (x : 𝕜) (s : Set 𝕜)
  proof: (p.hasDerivAt x).hasDerivWithinAt

中文:
定理 hasDerivWithinAt
  条件: (x : 𝕜) (s : 集合 𝕜)
  证明: (p.hasDerivAt x).hasDerivWithinAt
-/
protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt

/--
theorem `hasDerivWithinAt_aeval` / 定理 `hasDerivWithinAt_aeval`

English:
theorem hasDerivWithinAt_aeval
  given: (x : 𝕜) (s : Set 𝕜)
  proof: (q.hasDerivAt_aeval x).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_aeval
  条件: (x : 𝕜) (s : 集合 𝕜)
  证明: (q.hasDerivAt_aeval x).hasDerivWithinAt
-/
protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  statement: DifferentiableAt 𝕜 (fun x => p.eval x) x
  proof: (p.hasDerivAt x).differentiableAt

中文:
定理 differentiableAt
  结论: DifferentiableAt 𝕜 (fun x => p.eval x) x
  证明: (p.hasDerivAt x).differentiableAt
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt

/--
theorem `differentiableAt_aeval` / 定理 `differentiableAt_aeval`

English:
theorem differentiableAt_aeval
  statement: DifferentiableAt 𝕜 (fun x => aeval x q) x
  proof: (q.hasDerivAt_aeval x).differentiableAt

中文:
定理 differentiableAt_aeval
  结论: DifferentiableAt 𝕜 (fun x => aeval x q) x
  证明: (q.hasDerivAt_aeval x).differentiableAt
-/
protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt

/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  statement: DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x
  proof: p.differentiableAt.differentiableWithinAt

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x
  证明: p.differentiableAt.differentiableWithinAt
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt

/--
theorem `differentiableWithinAt_aeval` / 定理 `differentiableWithinAt_aeval`

English:
theorem differentiableWithinAt_aeval
  proof: q.differentiableAt_aeval.differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_aeval
  证明: q.differentiableAt_aeval.differentiableWithinAt

@[fun_prop]
-/
protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt

@[fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  statement: Differentiable 𝕜 fun x => p.eval x
  proof: fun _ => p.differentiableAt

中文:
定理 differentiable
  结论: 可微 𝕜 fun x => p.eval x
  证明: fun _ => p.differentiableAt
-/
protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt

/--
theorem `differentiable_aeval` / 定理 `differentiable_aeval`

English:
theorem differentiable_aeval
  statement: Differentiable 𝕜 fun x : 𝕜 => aeval x q
  proof: fun _ =>
  q.differentiableAt_aeval

中文:
定理 differentiable_aeval
  结论: 可微 𝕜 fun x : 𝕜 => aeval x q
  证明: fun _ =>
  q.differentiableAt_aeval
-/
protected theorem differentiable_aeval : Differentiable 𝕜 fun x : 𝕜 => aeval x q := fun _ =>
  q.differentiableAt_aeval

/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  statement: DifferentiableOn 𝕜 (fun x => p.eval x) s
  proof: p.differentiable.differentiableOn

中文:
定理 differentiableOn
  结论: DifferentiableOn 𝕜 (fun x => p.eval x) s
  证明: p.differentiable.differentiableOn
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.differentiable.differentiableOn

/--
theorem `differentiableOn_aeval` / 定理 `differentiableOn_aeval`

English:
theorem differentiableOn_aeval
  statement: DifferentiableOn 𝕜 (fun x => aeval x q) s
  proof: q.differentiable_aeval.differentiableOn

@[simp]

中文:
定理 differentiableOn_aeval
  结论: DifferentiableOn 𝕜 (fun x => aeval x q) s
  证明: q.differentiable_aeval.differentiableOn

@[simp]
-/
protected theorem differentiableOn_aeval : DifferentiableOn 𝕜 (fun x => aeval x q) s :=
  q.differentiable_aeval.differentiableOn

@[simp]
/--
theorem `deriv` / 定理 `deriv`

English:
theorem deriv
  statement: deriv (fun x => p.eval x) x = p.derivative.eval x
  proof: (p.hasDerivAt x).deriv

@[simp]

中文:
定理 deriv
  结论: deriv (fun x => p.eval x) x = p.derivative.eval x
  证明: (p.hasDerivAt x).deriv

@[simp]
-/
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.hasDerivAt x).deriv

@[simp]
/--
theorem `deriv_aeval` / 定理 `deriv_aeval`

English:
theorem deriv_aeval
  statement: deriv (fun x => aeval x q) x = aeval x (derivative q)
  proof: (q.hasDerivAt_aeval x).deriv

中文:
定理 deriv_aeval
  结论: deriv (fun x => aeval x q) x = aeval x (derivative q)
  证明: (q.hasDerivAt_aeval x).deriv
-/
protected theorem deriv_aeval : deriv (fun x => aeval x q) x = aeval x (derivative q) :=
  (q.hasDerivAt_aeval x).deriv

/--
theorem `derivWithin` / 定理 `derivWithin`

English:
theorem derivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv

中文:
定理 derivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv
-/
protected theorem derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv

/--
theorem `derivWithin_aeval` / 定理 `derivWithin_aeval`

English:
theorem derivWithin_aeval
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs

中文:
定理 derivWithin_aeval
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs
-/
protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => aeval x q) s x = aeval x (derivative q) := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs

/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  given: (x : 𝕜)
  proof: p.hasDerivAt x

中文:
定理 hasFDerivAt
  条件: (x : 𝕜)
  证明: p.hasDerivAt x
-/
protected theorem hasFDerivAt (x : 𝕜) :
    HasFDerivAt (fun x => p.eval x) (smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.hasDerivAt x

/--
theorem `hasFDerivAt_aeval` / 定理 `hasFDerivAt_aeval`

English:
theorem hasFDerivAt_aeval
  given: (x : 𝕜)
  proof: q.hasDerivAt_aeval x

中文:
定理 hasFDerivAt_aeval
  条件: (x : 𝕜)
  证明: q.hasDerivAt_aeval x
-/
protected theorem hasFDerivAt_aeval (x : 𝕜) :
    HasFDerivAt (fun x => aeval x q) (smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (aeval x (derivative q))) x :=
  q.hasDerivAt_aeval x

/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  given: (x : 𝕜)
  proof: (p.hasFDerivAt x).hasFDerivWithinAt

中文:
定理 hasFDerivWithinAt
  条件: (x : 𝕜)
  证明: (p.hasFDerivAt x).hasFDerivWithinAt
-/
protected theorem hasFDerivWithinAt (x : 𝕜) :
    HasFDerivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt

/--
theorem `hasFDerivWithinAt_aeval` / 定理 `hasFDerivWithinAt_aeval`

English:
theorem hasFDerivWithinAt_aeval
  given: (x : 𝕜)
  proof: (q.hasFDerivAt_aeval x).hasFDerivWithinAt

@[simp]

中文:
定理 hasFDerivWithinAt_aeval
  条件: (x : 𝕜)
  证明: (q.hasFDerivAt_aeval x).hasFDerivWithinAt

@[simp]
-/
protected theorem hasFDerivWithinAt_aeval (x : 𝕜) :
    HasFDerivWithinAt (fun x => aeval x q) (smulRight (1 : 𝕜 ->L[𝕜] 𝕜)
      (aeval x (derivative q))) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt

@[simp]
/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  proof: (p.hasFDerivAt x).fderiv

@[simp]

中文:
定理 fderiv
  证明: (p.hasFDerivAt x).fderiv

@[simp]
-/
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivAt x).fderiv

@[simp]
/--
theorem `fderiv_aeval` / 定理 `fderiv_aeval`

English:
theorem fderiv_aeval
  proof: (q.hasFDerivAt_aeval x).fderiv

中文:
定理 fderiv_aeval
  证明: (q.hasFDerivAt_aeval x).fderiv
-/
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivAt_aeval x).fderiv

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (p.hasFDerivWithinAt x).fderivWithin hxs

中文:
定理 fderivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (p.hasFDerivWithinAt x).fderivWithin hxs
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivWithinAt x).fderivWithin hxs

/--
theorem `fderivWithin_aeval` / 定理 `fderivWithin_aeval`

English:
theorem fderivWithin_aeval
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (q.hasFDerivWithinAt_aeval x).fderivWithin hxs

中文:
定理 fderivWithin_aeval
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (q.hasFDerivWithinAt_aeval x).fderivWithin hxs
-/
protected theorem fderivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = smulRight (1 : 𝕜 ->L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs

end Polynomial
