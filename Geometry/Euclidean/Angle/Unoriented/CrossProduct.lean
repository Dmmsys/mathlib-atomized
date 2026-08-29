/-
Copyright (c) 2020 Vedant Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vedant Gupta, Thomas Browning, Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Norm of cross-products

This file proves `InnerProductGeometry.norm_withLpEquiv_crossProduct`, relating the norm of the
cross-product of two real vectors with their individual norms.
-/

public section

open Matrix Real WithLp

namespace InnerProductGeometry

open scoped RealInnerProductSpace

/--
lemma `norm_ofLp_crossProduct` / 引理 `norm_ofLp_crossProduct`

English:
lemma norm_ofLp_crossProduct
  given: (a b : EuclideanSpace Real (Fin 3))
  proof: by
  have := sin_angle_nonneg a b
.mp ?_ refine sq_eq_sq₀ (by positivity) (by positivity)
  trans ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2
  · simp_rw [norm_sq_eq_re_inner (𝕜 := Real), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, cross_dot_cross, dotProduct_comm (ofLp b) (of

中文:
引理 norm_ofLp_crossProduct
  条件: (a b : EuclideanSpace 实数 (有限集 3))
  证明: by
  have := sin_angle_nonneg a b
.mp ?_ refine sq_eq_sq₀ (by positivity) (by positivity)
  trans ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2
  · simp_rw [norm_sq_eq_re_inner (𝕜 := Real), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, cross_dot_cross, dotProduct_comm (ofLp b) (of

Depends on / 依赖: EuclideanSpace, EuclideanSpace.inner_eq_star_dotProduct, RCLike, RCLike.re_to_real, cos_angle_mul_norm_mul_norm, cross_dot_cross, dotProduct_comm, inner_eq_star_dotProduct, linear_combination, norm_sq_eq_re_inner, re_to_real, simp_rw, sin_angle_nonneg, sin_sq_add_cos_sq, star_trivial
-/
lemma norm_ofLp_crossProduct (a b : EuclideanSpace Real (Fin 3)) :
    ‖toLp 2 (ofLp a ⨯₃ ofLp b)‖ = ‖a‖ * ‖b‖ * sin (angle a b) := by
  have := sin_angle_nonneg a b
.mp ?_ refine sq_eq_sq₀ (by positivity) (by positivity)
  trans ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2
  · simp_rw [norm_sq_eq_re_inner (𝕜 := Real), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, cross_dot_cross, dotProduct_comm (ofLp b) (ofLp a), sq]
  · linear_combination (‖a‖ * ‖b‖) ^ 2 * (sin_sq_add_cos_sq (angle a b)).symm +
      congrArg (· ^ 2) (cos_angle_mul_norm_mul_norm a b)

/--
lemma `norm_toLp_symm_crossProduct` / 引理 `norm_toLp_symm_crossProduct`

English:
lemma norm_toLp_symm_crossProduct
  given: (a b : Fin 3 -> Real)
  proof: by
  simp [← norm_ofLp_crossProduct (toLp 2 a) (toLp 2 b)]

中文:
引理 norm_toLp_symm_crossProduct
  条件: (a b : 有限集 3 -> 实数)
  证明: by
  simp [← norm_ofLp_crossProduct (toLp 2 a) (toLp 2 b)]

Depends on / 依赖: norm_ofLp_crossProduct
-/
lemma norm_toLp_symm_crossProduct (a b : Fin 3 -> Real) :
    ‖toLp 2 (a ⨯₃ b)‖ = ‖toLp 2 a‖ * ‖toLp 2 b‖ * sin (angle (toLp 2 a) (toLp 2 b)) := by
  simp [← norm_ofLp_crossProduct (toLp 2 a) (toLp 2 b)]

end InnerProductGeometry
