/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient
/-!
# Jacobson radical of polynomial ring

-/

public section

namespace Ideal

section Polynomial

open Polynomial

variable {R : Type*} [CommRing R]

/--
theorem `jacobson_bot_polynomial_le_sInf_map_maximal` / 定理 `jacobson_bot_polynomial_le_sInf_map_maximal`

English:
theorem jacobson_bot_polynomial_le_sInf_map_maximal
  proof: by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  have : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson <= J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2]; rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
have r1 : (X : (R ⧸ j)[X]) != 0 := ne_of_apply_ne (coeff · 1) by simp
  simpa [r1] using eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))

中文:
定理 jacobson_bot_polynomial_le_sInf_map_maximal
  证明: by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  have : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson <= J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2]; rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
have r1 : (X : (R ⧸ j)[X]) != 0 := ne_of_apply_ne (coeff · 1) by simp
  simpa [r1] using eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))

Depends on / 依赖: IsMaximal, J.jacobson, Polynomial, RingEquiv, RingEquiv.bijective, Trans.trans, bijective, bot_le, congr_arg, eq_bot_if, exists_imp, j.IsMaximal, jacobson, jacobson_eq_iff_jacobson_quotient_eq_bot, jacobson_mono, le_of_eq, le_sInf, map_bot, map_jacobson_of_bijective, polynomialQuotientEquivQuotientPolynomial
-/
theorem jacobson_bot_polynomial_le_sInf_map_maximal :
    jacobson (⊥ : Ideal R[X]) <= sInf (map (C : R ->+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  have : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson <= J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2]; rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
have r1 : (X : (R ⧸ j)[X]) != 0 := ne_of_apply_ne (coeff · 1) by simp
  simpa [r1] using eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))

/--
theorem `jacobson_bot_polynomial_of_jacobson_bot` / 定理 `jacobson_bot_polynomial_of_jacobson_bot`

English:
theorem jacobson_bot_polynomial_of_jacobson_bot
  given: (h : jacobson (⊥ : Ideal R) = ⊥)
  proof: by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
refine fun f hf => (Submodule.mem_bot R[X]).2 Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n in Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

中文:
定理 jacobson_bot_polynomial_of_jacobson_bot
  条件: (h : jacobson (⊥ : 理想 R) = ⊥)
  证明: by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
refine fun f hf => (Submodule.mem_bot R[X]).2 Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n in Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

Depends on / 依赖: Ideal.jacobson, Polynomial, Polynomial.ext, Submodule, Submodule.mem_bot, Trans.trans, coeff_zero, eq_bot_iff, f.coeff, jacobson, jacobson_bot_polynomial_le_sInf_map_maximal, le_trans, mem_bot, mem_map_C_iff, mem_sInf
-/
theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
    jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
refine fun f hf => (Submodule.mem_bot R[X]).2 Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n in Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

end Ideal
