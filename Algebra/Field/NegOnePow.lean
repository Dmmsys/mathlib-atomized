/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.NormNum

/-! # Integer powers of `-1` in a field -/

public section

namespace Int

/--
lemma `cast_negOnePow` / 引理 `cast_negOnePow`

English:
lemma cast_negOnePow
  given: (K : Type*) (n : Int) [DivisionRing K]
  statement: n.negOnePow = (-1 : K) ^ n
  proof: by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [zpow_mul, zpow_ofNat]
  · rw [zpow_add_one₀ (by simp), zpow_mul, zpow_ofNat]
    simp

中文:
引理 cast_negOnePow
  条件: (K : 类型) (n : 整数) [DivisionRing K]
  结论: n.negOnePow = (-1 : K) ^ n
  证明: by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [zpow_mul, zpow_ofNat]
  · rw [zpow_add_one₀ (by simp), zpow_mul, zpow_ofNat]
    simp

Depends on / 依赖: even_or_odd, zpow_mul, zpow_ofNat
-/
lemma cast_negOnePow (K : Type*) (n : Int) [DivisionRing K] : n.negOnePow = (-1 : K) ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [zpow_mul, zpow_ofNat]
  · rw [zpow_add_one₀ (by simp), zpow_mul, zpow_ofNat]
    simp

end Int
