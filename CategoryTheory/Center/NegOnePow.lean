/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Powers of `-1` in the center of a preadditive category

-/

public section

universe v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
@[simp]
/--
lemma `app_neg_one_zpow` / 引理 `app_neg_one_zpow`

English:
lemma app_neg_one_zpow
  given: (n : Int) (X : C)
  proof: by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

中文:
引理 app_neg_one_zpow
  条件: (n : 整数) (X : C)
  证明: by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

Depends on / 依赖: Even.add_self, Int.even_or_odd, Int.negOnePow_even, Int.negOnePow_odd, Int.two_mul, Units.smul_def, add_self, even_or_odd, mul_zpow, negOnePow_even, negOnePow_odd, odd_two_mul_add_one, smul_def, two_mul, zpow_add
-/
lemma app_neg_one_zpow (n : Int) (X : C) :
    ((-1) ^ n : (CatCenter C)ˣ).val.app X = n.negOnePow • 𝟙 X := by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

end CategoryTheory.CatCenter
