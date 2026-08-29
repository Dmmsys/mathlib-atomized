/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# Some results on dimensions of algebra adjoin

This file contains some results on dimensions of `Algebra.adjoin`.
-/

public section

open Module

universe u v

namespace Subalgebra

variable {R : Type u} {S : Type v} [CommRing R] [StrongRankCondition R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S) [Free R A] [Free R B]

/--
theorem `rank_sup_le_of_free` / 定理 `rank_sup_le_of_free`

English:
theorem rank_sup_le_of_free
  statement: Module.rank R ↥(A ⊔ B) <= Module.rank R A * Module.rank R B
  proof: by
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιB, bB⟩ := Free.exists_basis (R := R) (M := B)
  have h := Algebra.adjoin_union_coe_submodule R (A : Set S) (B : Set S)
  rw [A.adjoin_eq_span_basis R bA]; rw [B.adjoin_eq_span_basis R bB]; rw [← Algebra.sup_def]; rw [Submodule.sp

中文:
定理 rank_sup_le_of_free
  结论: 模.rank R ↥(A ⊔ B) <= 模.rank R A * 模.rank R B
  证明: by
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιB, bB⟩ := Free.exists_basis (R := R) (M := B)
  have h := Algebra.adjoin_union_coe_submodule R (A : Set S) (B : Set S)
  rw [A.adjoin_eq_span_basis R bA]; rw [B.adjoin_eq_span_basis R bB]; rw [← Algebra.sup_def]; rw [Submodule.sp

Depends on / 依赖: A.adjoin_eq_span_basis, Algebra, Algebra.adjoin_union_coe_submodule, Algebra.sup_def, B.adjoin_eq_span_basis, Cardinal, Cardinal.m, Cardinal.mk_mul_le, Free.exists_basis, Module, Module.rank, Submodule, Submodule.span_mul_span, adjoin_eq_span_basis, adjoin_union_coe_submodule, bA.mk_eq_rank, bB.mk_eq_rank, exists_basis, mk_eq_rank, mk_mul_le
-/
theorem rank_sup_le_of_free : Module.rank R ↥(A ⊔ B) <= Module.rank R A * Module.rank R B := by
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιB, bB⟩ := Free.exists_basis (R := R) (M := B)
  have h := Algebra.adjoin_union_coe_submodule R (A : Set S) (B : Set S)
  rw [A.adjoin_eq_span_basis R bA]; rw [B.adjoin_eq_span_basis R bB]; rw [← Algebra.sup_def]; rw [Submodule.span_mul_span] at h
  change Module.rank R ↥(toSubmodule (A ⊔ B)) <= _
  rw [h]; rw [← bA.mk_eq_rank'']; rw [← bB.mk_eq_rank'']
.trans ?_ refine (rank_span_le _).trans Cardinal.mk_mul_le
  gcongr <;> exact Cardinal.mk_range_le

/--
theorem `finrank_sup_le_of_free` / 定理 `finrank_sup_le_of_free`

English:
theorem finrank_sup_le_of_free
  statement: finrank R ↥(A ⊔ B) <= finrank R A * finrank R B
  proof: by
  by_cases h : Module.Finite R A ∧ Module.Finite R B
  · obtain ⟨_, _⟩ := h
    simpa only [map_mul] using! Cardinal.toNat_le_toNat (A.rank_sup_le_of_free B)
      (Cardinal.mul_lt_aleph0 (rank_lt_aleph0 R A) (rank_lt_aleph0 R B))
  wlog hA : ¬ Module.Finite R A generalizing A B
  · have := this 

中文:
定理 finrank_sup_le_of_free
  结论: finrank R ↥(A ⊔ B) <= finrank R A * finrank R B
  证明: by
  by_cases h : Module.Finite R A ∧ Module.Finite R B
  · obtain ⟨_, _⟩ := h
    simpa only [map_mul] using! Cardinal.toNat_le_toNat (A.rank_sup_le_of_free B)
      (Cardinal.mul_lt_aleph0 (rank_lt_aleph0 R A) (rank_lt_aleph0 R B))
  wlog hA : ¬ Module.Finite R A generalizing A B
  · have := this 

Depends on / 依赖: A.rank_sup_le_of_free, Cardinal, Cardinal.mul_lt_aleph0, Cardinal.toNat_le_toNat, Finite, LinearMap, LinearMap.rank_le_of_injective, Module, Module.Finite, Submodule, Submodule.inclusion_injective, generalizing, inclusion_injective, map_mul, mul_comm, mul_lt_aleph0, not_and, not_lt, of_not_not, rank_le_of_injective
-/
theorem finrank_sup_le_of_free : finrank R ↥(A ⊔ B) <= finrank R A * finrank R B := by
  by_cases h : Module.Finite R A ∧ Module.Finite R B
  · obtain ⟨_, _⟩ := h
    simpa only [map_mul] using! Cardinal.toNat_le_toNat (A.rank_sup_le_of_free B)
      (Cardinal.mul_lt_aleph0 (rank_lt_aleph0 R A) (rank_lt_aleph0 R B))
  wlog hA : ¬ Module.Finite R A generalizing A B
  · have := this B A (fun h' => h h'.symm) (not_and.1 h (of_not_not hA))
    rwa [sup_comm, mul_comm] at this
  rw [← rank_lt_aleph0_iff]; rw [not_lt] at hA
have := LinearMap.rank_le_of_injective _ Submodule.inclusion_injective
    show toSubmodule A <= toSubmodule (A ⊔ B) by simp
  rw [show finrank R A = 0 from Cardinal.toNat_apply_of_aleph0_le hA]; rw [show finrank R ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (hA.trans this)]; rw [zero_mul]

end Subalgebra
