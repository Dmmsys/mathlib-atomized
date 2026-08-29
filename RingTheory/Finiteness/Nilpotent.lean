/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

import Mathlib.Data.Fintype.Order

/-!
# Nilpotent maps on finite modules

-/

public section

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
theorem `Module.End.isNilpotent_iff_of_finite` / 定理 `Module.End.isNilpotent_iff_of_finite`

English:
theorem Module.End.isNilpotent_iff_of_finite
  given: [Module.Finite R M] {f : End R M}
  proof: by
  refine ⟨fun ⟨n, hn⟩ m => ⟨n, by simp [hn]⟩, fun h => ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m in Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact p

中文:
定理 模.End.isNilpotent_iff_of_finite
  条件: [模.有限 R M] {f : End R M}
  证明: by
  refine ⟨fun ⟨n, hn⟩ m => ⟨n, by simp [hn]⟩, fun h => ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m in Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact p

Depends on / 依赖: Finite, Finset, Finset.le_sup, Finset.sup, Module, Module.Finite.fg_top, Submodule, Submodule.span, Submodule.span_induction, fg_top, le_sup, pow_map_zero_of_le, span_induction
-/
theorem Module.End.isNilpotent_iff_of_finite [Module.Finite R M] {f : End R M} :
    IsNilpotent f ↔ forall m : M, exists n : Nat, (f ^ n) m = 0 := by
  refine ⟨fun ⟨n, hn⟩ m => ⟨n, by simp [hn]⟩, fun h => ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m in Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact pow_map_zero_of_le (Finset.le_sup hx) (hg x)
  | zero => simp
  | add => simp_all
  | smul => simp_all

namespace Matrix

open scoped Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {A : Matrix ι ι R}

@[simp]
/--
theorem `isNilpotent_transpose_iff` / 定理 `isNilpotent_transpose_iff`

English:
theorem isNilpotent_transpose_iff
  proof: by
  simp_rw [IsNilpotent, ← transpose_pow, transpose_eq_zero]

中文:
定理 isNilpotent_transpose_iff
  证明: by
  simp_rw [IsNilpotent, ← transpose_pow, transpose_eq_zero]

Depends on / 依赖: IsNilpotent, simp_rw, transpose_eq_zero, transpose_pow
-/
theorem isNilpotent_transpose_iff :
    IsNilpotent Aᵀ ↔ IsNilpotent A := by
  simp_rw [IsNilpotent, ← transpose_pow, transpose_eq_zero]

/--
theorem `isNilpotent_iff` / 定理 `isNilpotent_iff`

English:
theorem isNilpotent_iff
  proof: by
  simp_rw [← isNilpotent_toLin'_iff, Module.End.isNilpotent_iff_of_finite, ← toLin'_pow,
    toLin'_apply]

中文:
定理 isNilpotent_iff
  证明: by
  simp_rw [← isNilpotent_toLin'_iff, Module.End.isNilpotent_iff_of_finite, ← toLin'_pow,
    toLin'_apply]

Depends on / 依赖: Module, Module.End.isNilpotent_iff_of_finite, _apply, _iff, _pow, isNilpotent_iff_of_finite, isNilpotent_toLin, simp_rw
-/
theorem isNilpotent_iff :
    IsNilpotent A ↔ forall v, exists n : Nat, A ^ n *ᵥ v = 0 := by
  simp_rw [← isNilpotent_toLin'_iff, Module.End.isNilpotent_iff_of_finite, ← toLin'_pow,
    toLin'_apply]

/--
theorem `isNilpotent_iff_forall_row` / 定理 `isNilpotent_iff_forall_row`

English:
theorem isNilpotent_iff_forall_row
  proof: by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h v => ?_⟩
  · obtain ⟨n, hn⟩ := h (Pi.single i 1)
    exact ⟨n, by simpa [← transpose_pow] using hn⟩
  · choose n hn using h
    suffices forall i, (A ^ ⨆ j, n j) i = 0 from ⟨⨆ j, n j, by simp [mulVec_eq_sum, t

中文:
定理 isNilpotent_iff_对任意_row
  证明: by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h v => ?_⟩
  · obtain ⟨n, hn⟩ := h (Pi.single i 1)
    exact ⟨n, by simpa [← transpose_pow] using hn⟩
  · choose n hn using h
    suffices forall i, (A ^ ⨆ j, n j) i = 0 from ⟨⨆ j, n j, by simp [mulVec_eq_sum, t

Depends on / 依赖: Finite, Finite.le_ciSup, Pi.single, isNilpotent_iff, isNilpotent_transpose_iff, le_ciSup, mulVec_eq_sum, pow_row_eq_zero_of_le, single, transpose_pow
-/
theorem isNilpotent_iff_forall_row :
    IsNilpotent A ↔ forall i, exists n : Nat, (A ^ n).row i = 0 := by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h v => ?_⟩
  · obtain ⟨n, hn⟩ := h (Pi.single i 1)
    exact ⟨n, by simpa [← transpose_pow] using hn⟩
  · choose n hn using h
    suffices forall i, (A ^ ⨆ j, n j) i = 0 from ⟨⨆ j, n j, by simp [mulVec_eq_sum, this]⟩
    exact fun i => pow_row_eq_zero_of_le (hn i) (Finite.le_ciSup n i)

/--
theorem `isNilpotent_iff_forall_col` / 定理 `isNilpotent_iff_forall_col`

English:
theorem isNilpotent_iff_forall_col
  proof: by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff_forall_row]
  simp_rw [← transpose_pow, row_transpose]

中文:
定理 isNilpotent_iff_对任意_col
  证明: by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff_forall_row]
  simp_rw [← transpose_pow, row_transpose]

Depends on / 依赖: isNilpotent_iff_forall_row, isNilpotent_transpose_iff, row_transpose, simp_rw, transpose_pow
-/
theorem isNilpotent_iff_forall_col :
    IsNilpotent A ↔ forall i, exists n : Nat, (A ^ n).col i = 0 := by
  rw [← isNilpotent_transpose_iff]; rw [isNilpotent_iff_forall_row]
  simp_rw [← transpose_pow, row_transpose]

end Matrix
