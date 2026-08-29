/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.Action.Pointwise.Set

/-!
# Pointwise actions on sets in a ring

This file proves properties of pointwise actions on sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

open Module
open scoped Pointwise

variable {R G M : Type*}

namespace Finset
section Semiring
variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R} {m : M}

/--
lemma `zero_mem_smul_finset_iff` / 引理 `zero_mem_smul_finset_iff`

English:
lemma zero_mem_smul_finset_iff
  given: (hr : r != 0)
  statement: 0 in r • t ↔ 0 in t
  proof: by
  rw [← mem_coe]; rw [coe_smul_finset]; rw [Set.zero_mem_smul_set_iff hr]; rw [mem_coe]

中文:
引理 zero_mem_smul_finset_iff
  条件: (hr : r != 0)
  结论: 0 in r • t ↔ 0 in t
  证明: by
  rw [← mem_coe]; rw [coe_smul_finset]; rw [Set.zero_mem_smul_set_iff hr]; rw [mem_coe]

Depends on / 依赖: Set.zero_mem_smul_set_iff, coe_smul_finset, mem_coe, zero_mem_smul_set_iff
-/
lemma zero_mem_smul_finset_iff (hr : r != 0) : 0 in r • t ↔ 0 in t := by
  rw [← mem_coe]; rw [coe_smul_finset]; rw [Set.zero_mem_smul_set_iff hr]; rw [mem_coe]

/--
lemma `zero_mem_smul_iff` / 引理 `zero_mem_smul_iff`

English:
lemma zero_mem_smul_iff
  statement: (0 : M) in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.Nonempty
  proof: by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.zero_mem_smul_iff]; rfl

中文:
引理 zero_mem_smul_iff
  结论: (0 : M) in s • t ↔ 0 in s ∧ t.非空 ∨ 0 in t ∧ s.非空
  证明: by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.zero_mem_smul_iff]; rfl

Depends on / 依赖: Set.zero_mem_smul_iff, coe_smul, mem_coe, zero_mem_smul_iff
-/
lemma zero_mem_smul_iff : (0 : M) in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.Nonempty := by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.zero_mem_smul_iff]; rfl

end Semiring

variable [Ring R] [AddCommGroup G] [Module R G] [DecidableEq G] {s : Finset R} {t : Finset G}
  {a : R}

/--
lemma `neg_smul_finset` / 引理 `neg_smul_finset`

English:
lemma neg_smul_finset
  statement: -a • t = -(a • t)
  proof: by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]

中文:
引理 neg_smul_finset
  结论: -a • t = -(a • t)
  证明: by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]
-/
@[simp] lemma neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]

/--
lemma `neg_smul` / 引理 `neg_smul`

English:
lemma neg_smul
  given: [DecidableEq R]
  statement: -s • t = -(s • t)
  proof: by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul

中文:
引理 neg_smul
  条件: [DecidableEq R]
  结论: -s • t = -(s • t)
  证明: by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul
-/
@[simp] protected lemma neg_smul [DecidableEq R] : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul

end Finset
