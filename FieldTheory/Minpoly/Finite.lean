/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.FiniteType

/-!
# Minimal polynomials on a finite algebra

This file proves the bound on the degree of a minimal polynomial on an algebra
that is finite as a module.

-/

public section

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B] [Module.Finite A B] (x : B)

open Polynomial

namespace minpoly

variable (A) in
/--
theorem `natDegree_le_spanFinrank` / 定理 `natDegree_le_spanFinrank`

English:
theorem natDegree_le_spanFinrank
  proof: by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
exact Algebra.lmul_injective (R := A) by simpa using f_aeval

中文:
定理 natDegree_le_spanFinrank
  证明: by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
exact Algebra.lmul_injective (R := A) by simpa using f_aeval

Depends on / 依赖: Algebra, Algebra.lmul, Algebra.lmul_injective, LinearMap, LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero, aeval_algHom_apply, exists_monic_and_natDegree_eq_and_aeval_eq_zero, f_aeval, f_deg, f_monic, lmul_injective, minpoly, minpoly.min, natDegree_le_natDegree
-/
theorem natDegree_le_spanFinrank :
    (minpoly A x).natDegree <= (⊤ : Submodule A B).spanFinrank := by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
exact Algebra.lmul_injective (R := A) by simpa using f_aeval

/--
theorem `natDegree_le` / 定理 `natDegree_le`

English:
theorem natDegree_le
  given: [Module.Free A B]
  statement: (minpoly A x).natDegree <= Module.finrank A B
  proof: by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x

中文:
定理 natDegree_le
  条件: [Module.Free A B]
  结论: (minpoly A x).natDegree <= Module.finrank A B
  证明: by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x

Depends on / 依赖: Module, Module.finrank_eq_spanFinrank_of_free, finrank_eq_spanFinrank_of_free, natDegree_le_spanFinrank, nontriviality
-/
theorem natDegree_le [Module.Free A B] : (minpoly A x).natDegree <= Module.finrank A B := by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x

/--
theorem `degree_le` / 定理 `degree_le`

English:
theorem degree_le
  given: [Module.Free A B]
  statement: (minpoly A x).degree <= Module.finrank A B
  proof: degree_le_of_natDegree_le natDegree_le x

中文:
定理 degree_le
  条件: [Module.Free A B]
  结论: (minpoly A x).degree <= Module.finrank A B
  证明: degree_le_of_natDegree_le natDegree_le x

Depends on / 依赖: degree_le_of_natDegree_le, natDegree_le
-/
theorem degree_le [Module.Free A B] : (minpoly A x).degree <= Module.finrank A B :=
degree_le_of_natDegree_le natDegree_le x

end minpoly
