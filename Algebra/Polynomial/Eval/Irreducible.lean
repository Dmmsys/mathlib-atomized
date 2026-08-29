/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Prime.Defs

/-!
# Mapping irreducible polynomials

## Main results

* `Monic.irreducible_of_irreducible_map`: we can prove a monic polynomial is irreducible
  by mapping it to another integral domain and checking for irreducibility there.
-/

public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section
variable [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (φ : R ->+* S)

/--
lemma `Monic.irreducible_of_irreducible_map` / 引理 `Monic.irreducible_of_irreducible_map`

English:
lemma Monic.irreducible_of_irreducible_map
  statement: (f : R[X]) (h_mon : Monic f)
  proof: by
  refine ⟨h_irr.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b h => ?_⟩
  dsimp [Monic] at h_mon
  have q := (leadingCoeff_mul a b).symm
  rw [← h]; rw [h_mon] at q
  refine (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp ?_ ?_ <;>
      apply is

中文:
引理 Monic.irreducible_of_irreducible_map
  结论: (f : R[X]) (h_mon : Monic f)
  证明: by
  refine ⟨h_irr.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b h => ?_⟩
  dsimp [Monic] at h_mon
  have q := (leadingCoeff_mul a b).symm
  rw [← h]; rw [h_mon] at q
  refine (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp ?_ ?_ <;>
      apply is

Depends on / 依赖: IsUnit, IsUnit.map, IsUnit.of_mul_eq_one, Polynomial, Polynomial.map, Polynomial.map_mul, congr_arg, h_irr, h_irr.isUnit_or_isUnit, h_irr.not_isUnit, h_mon, isUnit_of_isUnit_leadingCoeff_of_isUnit_map, isUnit_or_isUnit, leadingCoeff_mul, mapRingHom, map_mul, mul_comm, not_isUnit, of_mul_eq_one
-/
lemma Monic.irreducible_of_irreducible_map (f : R[X]) (h_mon : Monic f)
    (h_irr : Irreducible (f.map φ)) : Irreducible f := by
  refine ⟨h_irr.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b h => ?_⟩
  dsimp [Monic] at h_mon
  have q := (leadingCoeff_mul a b).symm
  rw [← h]; rw [h_mon] at q
  refine (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp ?_ ?_ <;>
      apply isUnit_of_isUnit_leadingCoeff_of_isUnit_map <;>
    apply IsUnit.of_mul_eq_one
  · exact q
  · rw [mul_comm]
    exact q

end
end Polynomial
