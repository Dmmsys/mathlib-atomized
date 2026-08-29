/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.AdaptationNote

/-!
# Derivative of the inversion

In this file we prove a formula for the derivative of `EuclideanGeometry.inversion c R`.

## Implementation notes

Since `fderiv` and related definitions do not work for affine spaces, we deal with an inner product
space in this file.

## Keywords

inversion, derivative
-/

public section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]

open EuclideanGeometry

section DotNotation

variable {c x : E -> F} {R : E -> Real} {s : Set E} {a : E} {n : Nat∞}

/--
theorem `ContDiffWithinAt.inversion` / 定理 `ContDiffWithinAt.inversion`

English:
theorem ContDiffWithinAt.inversion
  statement: (hc : ContDiffWithinAt Real n c s a)
  proof: (((hR.div (hx.dist Real hc hne) (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

中文:
定理 ContDiffWithinAt.inversion
  结论: (hc : ContDiffWithinAt 实数 n c s a)
  证明: (((hR.div (hx.dist Real hc hne) (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc
-/
protected theorem ContDiffWithinAt.inversion (hc : ContDiffWithinAt Real n c s a)
    (hR : ContDiffWithinAt Real n R s a) (hx : ContDiffWithinAt Real n x s a) (hne : x a != c a) :
    ContDiffWithinAt Real n (fun a => inversion (c a) (R a) (x a)) s a :=
  (((hR.div (hx.dist Real hc hne) (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

/--
theorem `ContDiffOn.inversion` / 定理 `ContDiffOn.inversion`

English:
theorem ContDiffOn.inversion
  statement: (hc : ContDiffOn Real n c s) (hR : ContDiffOn Real n R s)
  proof: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected nonrec theorem ContDiffAt.inversion (hc : ContDiffAt Real n c a) (hR : ContDiffAt Real n R a)
    (hx : ContDiffAt Real n x a) (hne : x a != c a) :
    ContDiffAt Real n (fun a => inversion (c a) (R a) (x a)) a :=
  hc.inver

中文:
定理 ContDiffOn.inversion
  结论: (hc : ContDiffOn 实数 n c s) (hR : ContDiffOn 实数 n R s)
  证明: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected nonrec theorem ContDiffAt.inversion (hc : ContDiffAt Real n c a) (hR : ContDiffAt Real n R a)
    (hx : ContDiffAt Real n x a) (hne : x a != c a) :
    ContDiffAt Real n (fun a => inversion (c a) (R a) (x a)) a :=
  hc.inver
-/
protected theorem ContDiffOn.inversion (hc : ContDiffOn Real n c s) (hR : ContDiffOn Real n R s)
    (hx : ContDiffOn Real n x s) (hne : forall a in s, x a != c a) :
    ContDiffOn Real n (fun a => inversion (c a) (R a) (x a)) s := fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected nonrec theorem ContDiffAt.inversion (hc : ContDiffAt Real n c a) (hR : ContDiffAt Real n R a)
    (hx : ContDiffAt Real n x a) (hne : x a != c a) :
    ContDiffAt Real n (fun a => inversion (c a) (R a) (x a)) a :=
  hc.inversion hR hx hne

protected nonrec theorem ContDiff.inversion (hc : ContDiff Real n c) (hR : ContDiff Real n R)
    (hx : ContDiff Real n x) (hne : forall a, x a != c a) :
    ContDiff Real n (fun a => inversion (c a) (R a) (x a)) :=
  contDiff_iff_contDiffAt.2 fun a => hc.contDiffAt.inversion hR.contDiffAt hx.contDiffAt (hne a)

/--
theorem `DifferentiableWithinAt.inversion` / 定理 `DifferentiableWithinAt.inversion`

English:
theorem DifferentiableWithinAt.inversion
  statement: (hc : DifferentiableWithinAt Real c s a)
  proof: -- TODO: Use `.div` https://github.com/leanprover-community/mathlib4/issues/5870
  (((hR.mul <| (hx.dist Real hc hne).inv (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

中文:
定理 DifferentiableWithinAt.inversion
  结论: (hc : DifferentiableWithinAt 实数 c s a)
  证明: -- TODO: Use `.div` https://github.com/leanprover-community/mathlib4/issues/5870
  (((hR.mul <| (hx.dist Real hc hne).inv (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc
-/
protected theorem DifferentiableWithinAt.inversion (hc : DifferentiableWithinAt Real c s a)
    (hR : DifferentiableWithinAt Real R s a) (hx : DifferentiableWithinAt Real x s a) (hne : x a != c a) :
    DifferentiableWithinAt Real (fun a => inversion (c a) (R a) (x a)) s a :=
  -- TODO: Use `.div` https://github.com/leanprover-community/mathlib4/issues/5870
  (((hR.mul <| (hx.dist Real hc hne).inv (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

/--
theorem `DifferentiableOn.inversion` / 定理 `DifferentiableOn.inversion`

English:
theorem DifferentiableOn.inversion
  statement: (hc : DifferentiableOn Real c s)
  proof: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

中文:
定理 DifferentiableOn.inversion
  结论: (hc : DifferentiableOn 实数 c s)
  证明: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)
-/
protected theorem DifferentiableOn.inversion (hc : DifferentiableOn Real c s)
    (hR : DifferentiableOn Real R s) (hx : DifferentiableOn Real x s) (hne : forall a in s, x a != c a) :
    DifferentiableOn Real (fun a => inversion (c a) (R a) (x a)) s := fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

/--
theorem `DifferentiableAt.inversion` / 定理 `DifferentiableAt.inversion`

English:
theorem DifferentiableAt.inversion
  statement: (hc : DifferentiableAt Real c a)
  proof: by
  rw [← differentiableWithinAt_univ] at *
  exact hc.inversion hR hx hne

中文:
定理 DifferentiableAt.inversion
  结论: (hc : DifferentiableAt 实数 c a)
  证明: by
  rw [← differentiableWithinAt_univ] at *
  exact hc.inversion hR hx hne
-/
protected theorem DifferentiableAt.inversion (hc : DifferentiableAt Real c a)
    (hR : DifferentiableAt Real R a) (hx : DifferentiableAt Real x a) (hne : x a != c a) :
    DifferentiableAt Real (fun a => inversion (c a) (R a) (x a)) a := by
  rw [← differentiableWithinAt_univ] at *
  exact hc.inversion hR hx hne

/--
theorem `Differentiable.inversion` / 定理 `Differentiable.inversion`

English:
theorem Differentiable.inversion
  statement: (hc : Differentiable Real c)
  proof: fun a =>
  (hc a).inversion (hR a) (hx a) (hne a)

中文:
定理 Differentiable.inversion
  结论: (hc : Differentiable 实数 c)
  证明: fun a =>
  (hc a).inversion (hR a) (hx a) (hne a)
-/
protected theorem Differentiable.inversion (hc : Differentiable Real c)
    (hR : Differentiable Real R) (hx : Differentiable Real x) (hne : forall a, x a != c a) :
    Differentiable Real (fun a => inversion (c a) (R a) (x a)) := fun a =>
  (hc a).inversion (hR a) (hx a) (hne a)

end DotNotation

namespace EuclideanGeometry

variable {c x : F} {R : Real}

/--
theorem `hasFDerivAt_inversion` / 定理 `hasFDerivAt_inversion`

English:
theorem hasFDerivAt_inversion
  given: (hx : x != c)
  proof: by
  rcases add_left_surjective c x with ⟨x, rfl⟩
  have : HasFDerivAt (inversion c R) (?_ : F ->L[Real] F) (c + x) := by
    simp +unfoldPartialApp only [inversion]
    simp_rw [dist_eq_norm, div_pow, div_eq_mul_inv]
    have A := (hasFDerivAt_id (𝕜 := Real) (c + x)).sub_const c
    have B := ((has

中文:
定理 hasFDerivAt_inversion
  条件: (hx : x != c)
  证明: by
  rcases add_left_surjective c x with ⟨x, rfl⟩
  have : HasFDerivAt (inversion c R) (?_ : F ->L[Real] F) (c + x) := by
    simp +unfoldPartialApp only [inversion]
    simp_rw [dist_eq_norm, div_pow, div_eq_mul_inv]
    have A := (hasFDerivAt_id (𝕜 := Real) (c + x)).sub_const c
    have B := ((has

Depends on / 依赖: A.norm_sq, B.smul, HasFDerivAt, LinearMap, LinearMap.ext_on_codisjoint, Submodule, Submodule.isCompl_orthogonal, add_const, add_left_surjective, codisjoint, comp_hasFDerivAt, congr_fderiv, const_mul, dist_eq_norm, div_eq_mul_inv, div_pow, ext_on_codisjoint, hasDerivAt_inv, hasFDerivAt_id, inversion
-/
theorem hasFDerivAt_inversion (hx : x != c) :
    HasFDerivAt (inversion c R)
      ((R / dist x c) ^ 2 • ((Real ∙ (x - c))ᗮ.reflection : F ->L[Real] F)) x := by
  rcases add_left_surjective c x with ⟨x, rfl⟩
  have : HasFDerivAt (inversion c R) (?_ : F ->L[Real] F) (c + x) := by
    simp +unfoldPartialApp only [inversion]
    simp_rw [dist_eq_norm, div_pow, div_eq_mul_inv]
    have A := (hasFDerivAt_id (𝕜 := Real) (c + x)).sub_const c
    have B := ((hasDerivAt_inv <| by simpa using hx).comp_hasFDerivAt _ A.norm_sq).const_mul
      (R ^ 2)
    exact (B.smul A).add_const c
  refine this.congr_fderiv (LinearMap.ext_on_codisjoint
    (Submodule.isCompl_orthogonal (Real ∙ x)).codisjoint
    (LinearMap.eqOn_span' ?_) fun y hy => ?_)
  · have : ((‖x‖ ^ 2) ^ 2)⁻¹ * (‖x‖ ^ 2) = (‖x‖ ^ 2)⁻¹ := by
      rw [← div_eq_inv_mul]; rw [sq (‖x‖ ^ 2)]; rw [div_self_mul_self']
    simp [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      two_mul, this, div_eq_mul_inv, mul_add, add_smul, mul_pow]
  · simp [Submodule.mem_orthogonal_singleton_iff_inner_right.1 hy,
      Submodule.reflection_mem_subspace_eq_self hy, div_eq_mul_inv, mul_pow]

end EuclideanGeometry
