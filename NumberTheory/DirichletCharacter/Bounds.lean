/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Bounds for values of Dirichlet characters

We consider Dirichlet characters `χ` with values in a normed field `F`.

We show that `‖χ a‖ = 1` if `a` is a unit and `‖χ a‖ ≤ 1` in general.
-/

public section

variable {F : Type*} [NormedField F] {n : Nat} (χ : DirichletCharacter F n)

namespace DirichletCharacter

/--
lemma `unit_norm_eq_one` / 引理 `unit_norm_eq_one`

English:
lemma unit_norm_eq_one
  given: (a : (ZMod n)ˣ)
  statement: ‖χ a‖ = 1
  proof: by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow]; rw [← map_pow]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one']; rw [Units.val_one]; rw [map_one]; rw [norm_one]

中文:
引理 unit_norm_eq_one
  条件: (a : (ZMod n)ˣ)
  结论: ‖χ a‖ = 1
  证明: by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow]; rw [← map_pow]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one']; rw [Units.val_one]; rw [map_one]; rw [norm_one]
-/
@[simp] lemma unit_norm_eq_one (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow]; rw [← map_pow]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one']; rw [Units.val_one]; rw [map_one]; rw [norm_one]

/--
lemma `norm_le_one` / 引理 `norm_le_one`

English:
lemma norm_le_one
  given: (a : ZMod n)
  statement: ‖χ a‖ <= 1
  proof: by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one

中文:
引理 norm_le_one
  条件: (a : ZMod n)
  结论: ‖χ a‖ <= 1
  证明: by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one

Depends on / 依赖: IsUnit, h.unit, map_nonunit, norm_zero, unit_norm_eq_one, zero_le_one
-/
lemma norm_le_one (a : ZMod n) : ‖χ a‖ <= 1 := by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one


end DirichletCharacter
