/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Adjoin.FG

/-!
# Finitely generated subalgebras of a base change obtained from an element

## Main results
- `exists_fg_and_mem_baseChange`: given an element `x` of a tensor product `A ⊗[R] B` of two
  `R`-algebras `A` and `B`, there exists a finitely generated subalgebra `C` of `B` such that `x`
  is contained in `C ⊗[R] B`.

-/

public section

open TensorProduct

/--
lemma `exists_fg_and_mem_baseChange` / 引理 `exists_fg_and_mem_baseChange`

English:
lemma exists_fg_and_mem_baseChange
  statement: {R A B : Type*} [CommSemiring R]
  proof: by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin R (S.image fun j => j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs => (Subalgebra.tmul_mem_baseChange
      (Algebra.subset_adjoin (Finset.mem_image_of_mem _ hs)) s.1)

中文:
引理 存在_fg_and_mem_baseChange
  结论: {R A B : 类型} [交换半环 R]
  证明: by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin R (S.image fun j => j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs => (Subalgebra.tmul_mem_baseChange
      (Algebra.subset_adjoin (Finset.mem_image_of_mem _ hs)) s.1)

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Finset, Finset.mem_image_of_mem, S.image, Subalgebra, Subalgebra.fg_adjoin_finset, Subalgebra.sum_mem, Subalgebra.tmul_mem_baseChange, TensorProduct, TensorProduct.exists_finset, adjoin, classical, exists_finset, fg_adjoin_finset, mem_image_of_mem, subset_adjoin, sum_mem, tmul_mem_baseChange
-/
lemma exists_fg_and_mem_baseChange {R A B : Type*} [CommSemiring R]
    [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (x : A otimes[R] B) :
    exists C : Subalgebra R B, C.FG ∧ x in C.baseChange A := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin R (S.image fun j => j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs => (Subalgebra.tmul_mem_baseChange
      (Algebra.subset_adjoin (Finset.mem_image_of_mem _ hs)) s.1)
