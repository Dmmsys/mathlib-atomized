/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Polynomial modules in finite dimensions

This file is a place to collect results about the `R[X]`-module structure induced on an `R`-module
by an `R`-linear endomorphism, which require the concept of finite-dimensionality.

## Main results:
* `Module.AEval.isTorsion_of_finiteDimensional`: if a vector space `M` with coefficients in a field
  `K` carries a natural `K`-linear endomorphism which belongs to a finite-dimensional algebra
  over `K`, then the induced `K[X]`-module structure on `M` is pure torsion.

-/

public section

open Polynomial

variable {R K M A : Type*} {a : A}

namespace Module.AEval

/--
theorem `isTorsion_of_aeval_eq_zero` / 定理 `isTorsion_of_aeval_eq_zero`

English:
theorem isTorsion_of_aeval_eq_zero
  statement: [CommSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A]
  proof: by
  have hp : p in nonZeroDivisors R[X] := mem_nonZeroDivisors_iff_right.mpr
    fun q hq => Or.resolve_right (mul_eq_zero.mp hq) h'
exact fun x => ⟨⟨p, hp⟩, (of R M a).symm.injective by simp [h]⟩

中文:
定理 isTorsion_of_aeval_eq_zero
  结论: [CommSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A]
  证明: by
  have hp : p in nonZeroDivisors R[X] := mem_nonZeroDivisors_iff_right.mpr
    fun q hq => Or.resolve_right (mul_eq_zero.mp hq) h'
exact fun x => ⟨⟨p, hp⟩, (of R M a).symm.injective by simp [h]⟩

Depends on / 依赖: Or.resolve_right, injective, mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right.mpr, mul_eq_zero, mul_eq_zero.mp, nonZeroDivisors, resolve_right, symm.injective
-/
theorem isTorsion_of_aeval_eq_zero [CommSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
    {p : R[X]} (h : aeval a p = 0) (h' : p != 0) :
    IsTorsion R[X] (AEval R M a) := by
  have hp : p in nonZeroDivisors R[X] := mem_nonZeroDivisors_iff_right.mpr
    fun q hq => Or.resolve_right (mul_eq_zero.mp hq) h'
exact fun x => ⟨⟨p, hp⟩, (of R M a).symm.injective by simp [h]⟩

variable (K M a)

/--
theorem `isTorsion_of_finiteDimensional` / 定理 `isTorsion_of_finiteDimensional`

English:
theorem isTorsion_of_finiteDimensional
  statement: [Field K] [Ring A] [Algebra K A]
  proof: isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

中文:
定理 isTorsion_of_finiteDimensional
  结论: [Field K] [Ring A] [Algebra K A]
  证明: isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

Depends on / 依赖: isTorsion_of_aeval_eq_zero, minpoly, minpoly.aeval, minpoly.ne_zero_of_finite, ne_zero_of_finite
-/
theorem isTorsion_of_finiteDimensional [Field K] [Ring A] [Algebra K A]
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [FiniteDimensional K A] :
    IsTorsion K[X] (AEval K M a) :=
  isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

end Module.AEval
