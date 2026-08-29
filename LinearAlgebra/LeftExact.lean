/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Left Exactness of Hom


If `M1 → M2 → M3 → 0` is an exact sequence of `R`-modules and `N` is an `R`-module,
then `0 → (M3 →ₗ[R] N) → (M2 →ₗ[R] N) → (M1 →ₗ[R] N)` is exact. In this file, we
show the exactness at `M2 →ₗ[R] N` (`exact_lcomp_of_exact_of_surjective`);
the injectivity part is `LinearMap.lcomp_injective_of_surjective` in the file
`Mathlib.LinearAlgebra.BilinearMap`.


-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R] {M1 M2 M3 : Type*} (N : Type*)
  [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] [AddCommGroup N]
  [Module R M1] [Module R M2] [Module R M3] [Module R N]

/--
lemma `exact_lcomp_of_exact_of_surjective` / 引理 `exact_lcomp_of_exact_of_surjective`

English:
lemma exact_lcomp_of_exact_of_surjective
  statement: {f : M1 ->ₗ[R] M2} {g : M2 ->ₗ[R] M3}
  proof: by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh => ?_, fun ⟨y, hy⟩ => ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

中文:
引理 exact_lcomp_of_exact_of_surjective
  结论: {f : M1 ->ₗ[R] M2} {g : M2 ->ₗ[R] M3}
  证明: by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh => ?_, fun ⟨y, hy⟩ => ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.comp_zero, LinearMap.lcomp_apply, LinearMap.range, LinearMap.range_le_ker_iff.mpr, Set.mem_range, comp_assoc, comp_zero, exac.linearEquivOfSurjective, exac.linearMap_comp_eq_zero, lcomp_apply, linearEquivOfSurjective, linearMap_comp_eq_zero, mem_range, range_le_ker_iff, symm.toLinearMap, toLinearMap
-/
lemma exact_lcomp_of_exact_of_surjective {f : M1 ->ₗ[R] M2} {g : M2 ->ₗ[R] M3}
    (exac : Function.Exact f g) (surj : Function.Surjective g) :
    Function.Exact (LinearMap.lcomp R N g) (LinearMap.lcomp R N f) := by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh => ?_, fun ⟨y, hy⟩ => ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

end LinearMap
