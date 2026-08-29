/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Results relating rank and torsion.

-/

public section

/--
theorem `Module.IsTorsion.rank_eq_zero` / 定理 `Module.IsTorsion.rank_eq_zero`

English:
theorem Module.IsTorsion.rank_eq_zero
  statement: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: by
  by_contra! h'
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h'
  simpa [← map_smul, zero_notMem_nonZeroDivisors, hf] using @h (f 1)

中文:
定理 Module.IsTorsion.rank_eq_zero
  结论: {R M : 类型} [Semiring R] [AddCommMonoid M] [Module R M]
  证明: by
  by_contra! h'
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h'
  simpa [← map_smul, zero_notMem_nonZeroDivisors, hf] using @h (f 1)

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, map_smul, one_le_iff_ne_zero, one_le_rank_iff, zero_notMem_nonZeroDivisors
-/
theorem Module.IsTorsion.rank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : Module.rank R M = 0 := by
  by_contra! h'
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h'
  simpa [← map_smul, zero_notMem_nonZeroDivisors, hf] using @h (f 1)

/--
theorem `Module.IsTorsion.finrank_eq_zero` / 定理 `Module.IsTorsion.finrank_eq_zero`

English:
theorem Module.IsTorsion.finrank_eq_zero
  statement: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: finrank_eq_zero_of_rank_eq_zero h.rank_eq_zero

中文:
定理 Module.IsTorsion.finrank_eq_zero
  结论: {R M : 类型} [Semiring R] [AddCommMonoid M] [Module R M]
  证明: finrank_eq_zero_of_rank_eq_zero h.rank_eq_zero

Depends on / 依赖: finrank_eq_zero_of_rank_eq_zero, h.rank_eq_zero, rank_eq_zero
-/
theorem Module.IsTorsion.finrank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : finrank R M = 0 :=
  finrank_eq_zero_of_rank_eq_zero h.rank_eq_zero

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/--
lemma `Module.rank_eq_zero_iff_isTorsion` / 引理 `Module.rank_eq_zero_iff_isTorsion`

English:
lemma Module.rank_eq_zero_iff_isTorsion
  statement: Module.rank R M = 0 ↔ Module.IsTorsion R M
  proof: by
  simp [IsTorsion, rank_eq_zero_iff]

@[deprecated (since := "2026-07-14")] alias
rank_eq_zero_iff_isTorsion := Module.rank_eq_zero_iff_isTorsion

中文:
引理 Module.rank_eq_zero_iff_isTorsion
  结论: Module.rank R M = 0 ↔ Module.IsTorsion R M
  证明: by
  simp [IsTorsion, rank_eq_zero_iff]

@[deprecated (since := "2026-07-14")] alias
rank_eq_zero_iff_isTorsion := Module.rank_eq_zero_iff_isTorsion

Depends on / 依赖: IsTorsion, rank_eq_zero_iff
-/
lemma Module.rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  simp [IsTorsion, rank_eq_zero_iff]

@[deprecated (since := "2026-07-14")] alias
rank_eq_zero_iff_isTorsion := Module.rank_eq_zero_iff_isTorsion

/--
theorem `Module.finrank_eq_zero_iff_isTorsion` / 定理 `Module.finrank_eq_zero_iff_isTorsion`

English:
theorem Module.finrank_eq_zero_iff_isTorsion
  given: [StrongRankCondition R] [Module.Finite R M]
  proof: by
  simp [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]

中文:
定理 Module.finrank_eq_zero_iff_isTorsion
  条件: [StrongRankCondition R] [Module.Finite R M]
  证明: by
  simp [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]

Depends on / 依赖: finrank_eq_rank, rank_eq_zero_iff_isTorsion
-/
theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  simp [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
