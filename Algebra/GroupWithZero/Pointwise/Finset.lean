/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

public section

assert_not_exists MulAction Ring

open scoped Pointwise

namespace Finset
variable {α : Type*}

section Mul

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

/--
lemma `card_le_card_mul_left₀` / 引理 `card_le_card_mul_left₀`

English:
lemma card_le_card_mul_left₀
  given: [IsLeftCancelMulZero α] (has : a in s) (ha : a != 0)
  statement: #t <= #(s * t)
  proof: card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

中文:
引理 card_le_card_mul_left₀
  条件: [IsLeftCancelMulZero α] (has : a in s) (ha : a != 0)
  结论: #t <= #(s * t)
  证明: card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

Depends on / 依赖: card_le_card_mul_left_of_injective
-/
lemma card_le_card_mul_left₀ [IsLeftCancelMulZero α] (has : a in s) (ha : a != 0) : #t <= #(s * t) :=
  card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

/--
lemma `card_le_card_mul_right₀` / 引理 `card_le_card_mul_right₀`

English:
lemma card_le_card_mul_right₀
  given: [IsRightCancelMulZero α] (hat : a in t) (ha : a != 0)
  statement: #s <= #(s * t)
  proof: card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

中文:
引理 card_le_card_mul_right₀
  条件: [IsRightCancelMulZero α] (hat : a in t) (ha : a != 0)
  结论: #s <= #(s * t)
  证明: card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

Depends on / 依赖: card_le_card_mul_right_of_injective
-/
lemma card_le_card_mul_right₀ [IsRightCancelMulZero α] (hat : a in t) (ha : a != 0) : #s <= #(s * t) :=
  card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

/--
lemma `card_le_card_mul_self₀` / 引理 `card_le_card_mul_self₀`

English:
lemma card_le_card_mul_self₀
  given: [IsLeftCancelMulZero α]
  statement: #s <= #(s * s)
  proof: by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact card_le_card_mul_left₀ ha.2 ha.1

中文:
引理 card_le_card_mul_self₀
  条件: [IsLeftCancelMulZero α]
  结论: #s <= #(s * s)
  证明: by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact card_le_card_mul_left₀ ha.2 ha.1

Depends on / 依赖: eq_empty_or_nonempty, erase_eq_empty_iff, mem_erase, ne_eq, s.erase
-/
lemma card_le_card_mul_self₀ [IsLeftCancelMulZero α] : #s <= #(s * s) := by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact card_le_card_mul_left₀ ha.2 ha.1

end Mul

section MulZeroClass
variable [DecidableEq α] [MulZeroClass α] {s : Finset α}


/--
lemma `mul_zero_subset` / 引理 `mul_zero_subset`

English:
lemma mul_zero_subset
  given: (s : Finset α)
  statement: s * 0 subseteq 0
  proof: by simp [subset_iff, mem_mul]

中文:
引理 mul_zero_subset
  条件: (s : Finset α)
  结论: s * 0 subseteq 0
  证明: by simp [subset_iff, mem_mul]

Depends on / 依赖: mem_mul, subset_iff
-/
lemma mul_zero_subset (s : Finset α) : s * 0 subseteq 0 := by simp [subset_iff, mem_mul]
/--
lemma `zero_mul_subset` / 引理 `zero_mul_subset`

English:
lemma zero_mul_subset
  given: (s : Finset α)
  statement: 0 * s subseteq 0
  proof: by simp [subset_iff, mem_mul]

中文:
引理 zero_mul_subset
  条件: (s : Finset α)
  结论: 0 * s subseteq 0
  证明: by simp [subset_iff, mem_mul]

Depends on / 依赖: mem_mul, subset_iff
-/
lemma zero_mul_subset (s : Finset α) : 0 * s subseteq 0 := by simp [subset_iff, mem_mul]

/--
lemma `Nonempty.mul_zero` / 引理 `Nonempty.mul_zero`

English:
lemma Nonempty.mul_zero
  given: (hs : s.Nonempty)
  statement: s * 0 = 0
  proof: s.mul_zero_subset.antisymm by simpa [mem_mul] using! hs

中文:
引理 Nonempty.mul_zero
  条件: (hs : s.Nonempty)
  结论: s * 0 = 0
  证明: s.mul_zero_subset.antisymm by simpa [mem_mul] using! hs

Depends on / 依赖: antisymm, mem_mul, mul_zero_subset, s.mul_zero_subset.antisymm
-/
lemma Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm by simpa [mem_mul] using! hs

/--
lemma `Nonempty.zero_mul` / 引理 `Nonempty.zero_mul`

English:
lemma Nonempty.zero_mul
  given: (hs : s.Nonempty)
  statement: 0 * s = 0
  proof: s.zero_mul_subset.antisymm by simpa [mem_mul] using! hs

中文:
引理 Nonempty.zero_mul
  条件: (hs : s.Nonempty)
  结论: 0 * s = 0
  证明: s.zero_mul_subset.antisymm by simpa [mem_mul] using! hs

Depends on / 依赖: antisymm, mem_mul, s.zero_mul_subset.antisymm, zero_mul_subset
-/
lemma Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm by simpa [mem_mul] using! hs

end MulZeroClass

section GroupWithZero
variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

/--
lemma `div_zero_subset` / 引理 `div_zero_subset`

English:
lemma div_zero_subset
  given: (s : Finset α)
  statement: s / 0 subseteq 0
  proof: by simp [subset_iff, mem_div]

中文:
引理 div_zero_subset
  条件: (s : Finset α)
  结论: s / 0 subseteq 0
  证明: by simp [subset_iff, mem_div]

Depends on / 依赖: mem_div, subset_iff
-/
lemma div_zero_subset (s : Finset α) : s / 0 subseteq 0 := by simp [subset_iff, mem_div]

/--
lemma `zero_div_subset` / 引理 `zero_div_subset`

English:
lemma zero_div_subset
  given: (s : Finset α)
  statement: 0 / s subseteq 0
  proof: by simp [subset_iff, mem_div]

中文:
引理 zero_div_subset
  条件: (s : Finset α)
  结论: 0 / s subseteq 0
  证明: by simp [subset_iff, mem_div]

Depends on / 依赖: mem_div, subset_iff
-/
lemma zero_div_subset (s : Finset α) : 0 / s subseteq 0 := by simp [subset_iff, mem_div]

/--
lemma `Nonempty.div_zero` / 引理 `Nonempty.div_zero`

English:
lemma Nonempty.div_zero
  given: (hs : s.Nonempty)
  statement: s / 0 = 0
  proof: s.div_zero_subset.antisymm by simpa [mem_div] using! hs

中文:
引理 Nonempty.div_zero
  条件: (hs : s.Nonempty)
  结论: s / 0 = 0
  证明: s.div_zero_subset.antisymm by simpa [mem_div] using! hs

Depends on / 依赖: antisymm, div_zero_subset, mem_div, s.div_zero_subset.antisymm
-/
lemma Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
s.div_zero_subset.antisymm by simpa [mem_div] using! hs

/--
lemma `Nonempty.zero_div` / 引理 `Nonempty.zero_div`

English:
lemma Nonempty.zero_div
  given: (hs : s.Nonempty)
  statement: 0 / s = 0
  proof: s.zero_div_subset.antisymm by simpa [mem_div] using! hs

中文:
引理 Nonempty.zero_div
  条件: (hs : s.Nonempty)
  结论: 0 / s = 0
  证明: s.zero_div_subset.antisymm by simpa [mem_div] using! hs

Depends on / 依赖: antisymm, mem_div, s.zero_div_subset.antisymm, zero_div_subset
-/
lemma Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm by simpa [mem_div] using! hs

/--
lemma `inv_zero` / 引理 `inv_zero`

English:
lemma inv_zero
  statement: (0 : Finset α)⁻¹ = 0
  proof: by ext; simp

中文:
引理 inv_zero
  结论: (0 : Finset α)⁻¹ = 0
  证明: by ext; simp
-/
@[simp] protected lemma inv_zero : (0 : Finset α)⁻¹ = 0 := by ext; simp

end GroupWithZero
end Finset
