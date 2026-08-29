/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a group with zero

This file proves properties of pointwise operations of sets in a group with zero.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

assert_not_exists MulAction IsOrderedMonoid Ring

open Function
open scoped Pointwise

variable {α : Type*}

namespace Set

section MulZeroClass
variable [MulZeroClass α] {s : Set α}


/--
lemma `mul_zero_subset` / 引理 `mul_zero_subset`

English:
lemma mul_zero_subset
  given: (s : Set α)
  statement: s * 0 subseteq 0
  proof: by simp [subset_def, mem_mul]

中文:
引理 mul_zero_subset
  条件: (s : Set α)
  结论: s * 0 subseteq 0
  证明: by simp [subset_def, mem_mul]

Depends on / 依赖: mem_mul, subset_def
-/
lemma mul_zero_subset (s : Set α) : s * 0 subseteq 0 := by simp [subset_def, mem_mul]
/--
lemma `zero_mul_subset` / 引理 `zero_mul_subset`

English:
lemma zero_mul_subset
  given: (s : Set α)
  statement: 0 * s subseteq 0
  proof: by simp [subset_def, mem_mul]

中文:
引理 zero_mul_subset
  条件: (s : Set α)
  结论: 0 * s subseteq 0
  证明: by simp [subset_def, mem_mul]

Depends on / 依赖: mem_mul, subset_def
-/
lemma zero_mul_subset (s : Set α) : 0 * s subseteq 0 := by simp [subset_def, mem_mul]

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
-/
lemma Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm by simpa [mem_mul] using! hs

end MulZeroClass

section GroupWithZero
variable [GroupWithZero α] {s : Set α}

/--
lemma `div_zero_subset` / 引理 `div_zero_subset`

English:
lemma div_zero_subset
  given: (s : Set α)
  statement: s / 0 subseteq 0
  proof: by simp [subset_def, mem_div]

中文:
引理 div_zero_subset
  条件: (s : Set α)
  结论: s / 0 subseteq 0
  证明: by simp [subset_def, mem_div]

Depends on / 依赖: mem_div, subset_def
-/
lemma div_zero_subset (s : Set α) : s / 0 subseteq 0 := by simp [subset_def, mem_div]
/--
lemma `zero_div_subset` / 引理 `zero_div_subset`

English:
lemma zero_div_subset
  given: (s : Set α)
  statement: 0 / s subseteq 0
  proof: by simp [subset_def, mem_div]

中文:
引理 zero_div_subset
  条件: (s : Set α)
  结论: 0 / s subseteq 0
  证明: by simp [subset_def, mem_div]

Depends on / 依赖: mem_div, subset_def
-/
lemma zero_div_subset (s : Set α) : 0 / s subseteq 0 := by simp [subset_def, mem_div]

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
-/
lemma Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm by simpa [mem_div] using! hs

/--
lemma `inv_zero` / 引理 `inv_zero`

English:
lemma inv_zero
  statement: (0 : Set α)⁻¹ = 0
  proof: by ext; simp

中文:
引理 inv_zero
  结论: (0 : Set α)⁻¹ = 0
  证明: by ext; simp
-/
@[simp] protected lemma inv_zero : (0 : Set α)⁻¹ = 0 := by ext; simp

end GroupWithZero
end Set
