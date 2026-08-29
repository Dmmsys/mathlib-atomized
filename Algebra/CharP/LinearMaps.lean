/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Huanyu Zheng
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Characteristic of the ring of linear Maps

This file contains properties of the characteristic of the ring of linear maps.
The characteristic of the ring of linear maps is determined by its base ring.

## Main Results

- `Module.charP_end` : For a commutative semiring `R` and an `R`-module `M`,
  the characteristic of `R` is equal to the characteristic of the `R`-linear
  endomorphisms of `M` when `M` contains a non-torsion element `x`.

## Notation

- `R` is a commutative semiring
- `M` is an `R`-module

## Implementation Notes

One can also deduce similar result via `charP_of_injective_ringHom` and
  `R → (M →ₗ[R] M) : r ↦ (fun (x : M) ↦ r • x)`. But this will require stronger condition
  compared to `Module.charP_end`.

-/

public section

namespace Module

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
theorem `charP_end` / 定理 `charP_end`

English:
theorem charP_end
  statement: {p : Nat} [hchar : CharP R p]
  proof: by
    have exact : (n : M ->ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [exact]; rw [LinearMap.ext_iff]; rw [← hchar.1]
    exact ⟨fun h => htorsion.casesOn fun x hx => by simpa [← Ideal.mem_torsionOf_iff, hx] using h x,
      fun h => (congrArg (fun t => forall x, t • x = 0) h).mpr fun x => zero_smul R x⟩

中文:
定理 charP_end
  结论: {p : 自然数} [hchar : 特征p R p]
  证明: by
    have exact : (n : M ->ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [exact]; rw [LinearMap.ext_iff]; rw [← hchar.1]
    exact ⟨fun h => htorsion.casesOn fun x hx => by simpa [← Ideal.mem_torsionOf_iff, hx] using h x,
      fun h => (congrArg (fun t => forall x, t • x = 0) h).mpr fun x => zero_smul R x⟩

Depends on / 依赖: Ideal.mem_torsionOf_iff, LinearMap, LinearMap.ext_iff, Nat.cast_smul_eq_nsmul, casesOn, cast_smul_eq_nsmul, ext_iff, htorsion, htorsion.casesOn, mem_torsionOf_iff, mul_one, nsmul_eq_mul, zero_smul
-/
theorem charP_end {p : Nat} [hchar : CharP R p]
    (htorsion : exists x : M, Ideal.torsionOf R M x = ⊥) : CharP (M ->ₗ[R] M) p where
  cast_eq_zero_iff n := by
    have exact : (n : M ->ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [exact]; rw [LinearMap.ext_iff]; rw [← hchar.1]
    exact ⟨fun h => htorsion.casesOn fun x hx => by simpa [← Ideal.mem_torsionOf_iff, hx] using h x,
      fun h => (congrArg (fun t => forall x, t • x = 0) h).mpr fun x => zero_smul R x⟩

end Module

/-- For a division ring `D` with center `k`, the ring of `k`-linear endomorphisms
  of `D` has the same characteristic as `D` -/
instance {D : Type*} [DivisionRing D] {p : Nat} [CharP D p] :
    CharP (D ->ₗ[(Subring.center D)] D) p :=
  charP_of_injective_ringHom (Algebra.lmul (Subring.center D) D).toRingHom.injective p

instance {D : Type*} [DivisionRing D] {p : Nat} [ExpChar D p] :
    ExpChar (D ->ₗ[Subring.center D] D) p :=
  expChar_of_injective_ringHom (Algebra.lmul (Subring.center D) D).toRingHom.injective p
