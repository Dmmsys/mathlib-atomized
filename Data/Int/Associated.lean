/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Int.Units
/-!
# Associated elements and the integers

This file contains some results on equality up to units in the integers.

## Main results

* `Int.natAbs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/

public section


/--
theorem `Int.natAbs_eq_iff_associated` / 定理 `Int.natAbs_eq_iff_associated`

English:
theorem Int.natAbs_eq_iff_associated
  given: {a b : Int}
  statement: a.natAbs = b.natAbs ↔ Associated a b
  proof: by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)

中文:
定理 Int.natAbs_eq_iff_associated
  条件: {a b : 整数}
  结论: a.natAbs = b.natAbs ↔ Associated a b
  证明: by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)

Depends on / 依赖: Int.natAbs_eq_natAbs_iff.trans, Int.units_eq_one_or, Or.inl, Or.inr, natAbs_eq_natAbs_iff, units_eq_one_or
-/
theorem Int.natAbs_eq_iff_associated {a b : Int} : a.natAbs = b.natAbs ↔ Associated a b := by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
