/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Finset.Density

/-!
# Doubling and difference constants

This file defines the doubling and difference constants of two finsets in a group.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace Finset
section Group
variable {G G' : Type*} [Group G] [AddGroup G'] [DecidableEq G] [DecidableEq G'] {A B : Finset G}

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`.

The notation `σₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`.

The notation `σ[A, B]` is available in scope `Combinatorics.Additive`. -/]
/--
Definition of `mulConst` / `mulConst` 的定义

English:
definition mulConst
  signature: (A B : Finset G)
  body: #(A * B) / #A

中文:
定义 mulConst
  签名: (A B : Finset G)
  定义体: #(A * B) / #A
-/
def mulConst (A B : Finset G) : Rat>=0 := #(A * B) / #A

/-- The difference constant `δₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`.

The notation `δₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`.

The notation `δ[A, B]` is available in scope `Combinatorics.Additive`. -/]
/--
Definition of `divConst` / `divConst` 的定义

English:
definition divConst
  signature: (A B : Finset G)
  body: #(A / B) / #A

中文:
定义 divConst
  签名: (A B : Finset G)
  定义体: #(A / B) / #A
-/
def divConst (A B : Finset G) : Rat>=0 := #(A / B) / #A

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A ", " B "]" => Finset.mulConst A B

/-- The doubling constant `σₘ[A]` of a finset `A` in a group is `|A * A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A "]" => Finset.mulConst A A

/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A ", " B "]" => Finset.addConst A B

/-- The doubling constant `σ[A]` of a finset `A` in a group is `|A + A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A "]" => Finset.addConst A A

/-- The difference constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A ", " B "]" => Finset.divConst A B

/-- The difference constant `σₘ[A]` of a finset `A` in a group is `|A / A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A "]" => Finset.divConst A A

/-- The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A ", " B "]" => Finset.subConst A B

/-- The difference constant `σ[A]` of a finset `A` in a group is `|A - A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A "]" => Finset.subConst A A

open scoped Combinatorics.Additive

@[to_additive (attr := simp) addConst_mul_card]
/--
lemma `mulConst_mul_card` / 引理 `mulConst_mul_card`

English:
lemma mulConst_mul_card
  given: (A B : Finset G)
  statement: σₘ[A, B] * #A = #(A * B)
  proof: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) subConst_mul_card]

中文:
引理 mulConst_mul_card
  条件: (A B : Finset G)
  结论: σₘ[A, B] * #A = #(A * B)
  证明: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) subConst_mul_card]

Depends on / 依赖: A.eq_empty_or_nonempty, eq_empty_or_nonempty
-/
lemma mulConst_mul_card (A B : Finset G) : σₘ[A, B] * #A = #(A * B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) subConst_mul_card]
/--
lemma `divConst_mul_card` / 引理 `divConst_mul_card`

English:
lemma divConst_mul_card
  given: (A B : Finset G)
  statement: δₘ[A, B] * #A = #(A / B)
  proof: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) card_mul_addConst]

中文:
引理 divConst_mul_card
  条件: (A B : Finset G)
  结论: δₘ[A, B] * #A = #(A / B)
  证明: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) card_mul_addConst]

Depends on / 依赖: A.eq_empty_or_nonempty, eq_empty_or_nonempty
-/
lemma divConst_mul_card (A B : Finset G) : δₘ[A, B] * #A = #(A / B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) card_mul_addConst]
/--
lemma `card_mul_mulConst` / 引理 `card_mul_mulConst`

English:
lemma card_mul_mulConst
  given: (A B : Finset G)
  statement: #A * σₘ[A, B] = #(A * B)
  proof: by
  rw [mul_comm]; rw [mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]

中文:
引理 card_mul_mulConst
  条件: (A B : Finset G)
  结论: #A * σₘ[A, B] = #(A * B)
  证明: by
  rw [mul_comm]; rw [mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]

Depends on / 依赖: mulConst_mul_card, mul_comm
-/
lemma card_mul_mulConst (A B : Finset G) : #A * σₘ[A, B] = #(A * B) := by
  rw [mul_comm]; rw [mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]
/--
lemma `card_mul_divConst` / 引理 `card_mul_divConst`

English:
lemma card_mul_divConst
  given: (A B : Finset G)
  statement: #A * δₘ[A, B] = #(A / B)
  proof: by
  rw [mul_comm]; rw [divConst_mul_card]

@[to_additive (attr := simp)]

中文:
引理 card_mul_divConst
  条件: (A B : Finset G)
  结论: #A * δₘ[A, B] = #(A / B)
  证明: by
  rw [mul_comm]; rw [divConst_mul_card]

@[to_additive (attr := simp)]

Depends on / 依赖: divConst_mul_card, mul_comm
-/
lemma card_mul_divConst (A B : Finset G) : #A * δₘ[A, B] = #(A / B) := by
  rw [mul_comm]; rw [divConst_mul_card]

@[to_additive (attr := simp)]
/--
lemma `mulConst_empty_left` / 引理 `mulConst_empty_left`

English:
lemma mulConst_empty_left
  given: (B : Finset G)
  statement: σₘ[∅, B] = 0
  proof: by simp [mulConst]

@[to_additive (attr := simp)]

中文:
引理 mulConst_empty_left
  条件: (B : Finset G)
  结论: σₘ[∅, B] = 0
  证明: by simp [mulConst]

@[to_additive (attr := simp)]

Depends on / 依赖: mulConst
-/
lemma mulConst_empty_left (B : Finset G) : σₘ[∅, B] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
/--
lemma `divConst_empty_left` / 引理 `divConst_empty_left`

English:
lemma divConst_empty_left
  given: (B : Finset G)
  statement: δₘ[∅, B] = 0
  proof: by simp [divConst]

@[to_additive (attr := simp)]

中文:
引理 divConst_empty_left
  条件: (B : Finset G)
  结论: δₘ[∅, B] = 0
  证明: by simp [divConst]

@[to_additive (attr := simp)]

Depends on / 依赖: divConst
-/
lemma divConst_empty_left (B : Finset G) : δₘ[∅, B] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
/--
lemma `mulConst_empty_right` / 引理 `mulConst_empty_right`

English:
lemma mulConst_empty_right
  given: (A : Finset G)
  statement: σₘ[A, ∅] = 0
  proof: by simp [mulConst]

@[to_additive (attr := simp)]

中文:
引理 mulConst_empty_right
  条件: (A : Finset G)
  结论: σₘ[A, ∅] = 0
  证明: by simp [mulConst]

@[to_additive (attr := simp)]

Depends on / 依赖: mulConst
-/
lemma mulConst_empty_right (A : Finset G) : σₘ[A, ∅] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
/--
lemma `divConst_empty_right` / 引理 `divConst_empty_right`

English:
lemma divConst_empty_right
  given: (A : Finset G)
  statement: δₘ[A, ∅] = 0
  proof: by simp [divConst]

@[to_additive (attr := simp)]

中文:
引理 divConst_empty_right
  条件: (A : Finset G)
  结论: δₘ[A, ∅] = 0
  证明: by simp [divConst]

@[to_additive (attr := simp)]

Depends on / 依赖: divConst
-/
lemma divConst_empty_right (A : Finset G) : δₘ[A, ∅] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
/--
lemma `mulConst_inv_right` / 引理 `mulConst_inv_right`

English:
lemma mulConst_inv_right
  given: (A B : Finset G)
  statement: σₘ[A, B⁻¹] = δₘ[A, B]
  proof: by
  rw [mulConst]; rw [divConst]; rw [← div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
引理 mulConst_inv_right
  条件: (A B : Finset G)
  结论: σₘ[A, B⁻¹] = δₘ[A, B]
  证明: by
  rw [mulConst]; rw [divConst]; rw [← div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: divConst, div_eq_mul_inv, mulConst
-/
lemma mulConst_inv_right (A B : Finset G) : σₘ[A, B⁻¹] = δₘ[A, B] := by
  rw [mulConst]; rw [divConst]; rw [← div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
lemma `divConst_inv_right` / 引理 `divConst_inv_right`

English:
lemma divConst_inv_right
  given: (A B : Finset G)
  statement: δₘ[A, B⁻¹] = σₘ[A, B]
  proof: by
  rw [mulConst]; rw [divConst]; rw [div_inv_eq_mul]

@[to_additive]

中文:
引理 divConst_inv_right
  条件: (A B : Finset G)
  结论: δₘ[A, B⁻¹] = σₘ[A, B]
  证明: by
  rw [mulConst]; rw [divConst]; rw [div_inv_eq_mul]

@[to_additive]

Depends on / 依赖: divConst, div_inv_eq_mul, mulConst
-/
lemma divConst_inv_right (A B : Finset G) : δₘ[A, B⁻¹] = σₘ[A, B] := by
  rw [mulConst]; rw [divConst]; rw [div_inv_eq_mul]

@[to_additive]
/--
lemma `one_le_mulConst` / 引理 `one_le_mulConst`

English:
lemma one_le_mulConst
  given: (hA : A.Nonempty) (hB : B.Nonempty)
  statement: 1 <= σₘ[A, B]
  proof: by
  rw [mulConst]; rw [one_le_div₀]
  · exact mod_cast card_le_card_mul_right hB
  · simpa

@[to_additive]

中文:
引理 one_le_mulConst
  条件: (hA : A.Nonempty) (hB : B.Nonempty)
  结论: 1 <= σₘ[A, B]
  证明: by
  rw [mulConst]; rw [one_le_div₀]
  · exact mod_cast card_le_card_mul_right hB
  · simpa

@[to_additive]

Depends on / 依赖: card_le_card_mul_right, mod_cast, mulConst
-/
lemma one_le_mulConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 <= σₘ[A, B] := by
  rw [mulConst]; rw [one_le_div₀]
  · exact mod_cast card_le_card_mul_right hB
  · simpa

@[to_additive]
/--
lemma `one_le_mulConst_self` / 引理 `one_le_mulConst_self`

English:
lemma one_le_mulConst_self
  given: (hA : A.Nonempty)
  statement: 1 <= σₘ[A]
  proof: one_le_mulConst hA hA

@[to_additive]

中文:
引理 one_le_mulConst_self
  条件: (hA : A.Nonempty)
  结论: 1 <= σₘ[A]
  证明: one_le_mulConst hA hA

@[to_additive]

Depends on / 依赖: one_le_mulConst
-/
lemma one_le_mulConst_self (hA : A.Nonempty) : 1 <= σₘ[A] := one_le_mulConst hA hA

@[to_additive]
/--
lemma `one_le_divConst` / 引理 `one_le_divConst`

English:
lemma one_le_divConst
  given: (hA : A.Nonempty) (hB : B.Nonempty)
  statement: 1 <= δₘ[A, B]
  proof: by
  rw [← mulConst_inv_right]
  apply one_le_mulConst hA (by simpa)

@[to_additive]

中文:
引理 one_le_divConst
  条件: (hA : A.Nonempty) (hB : B.Nonempty)
  结论: 1 <= δₘ[A, B]
  证明: by
  rw [← mulConst_inv_right]
  apply one_le_mulConst hA (by simpa)

@[to_additive]

Depends on / 依赖: mulConst_inv_right, one_le_mulConst
-/
lemma one_le_divConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 <= δₘ[A, B] := by
  rw [← mulConst_inv_right]
  apply one_le_mulConst hA (by simpa)

@[to_additive]
/--
lemma `one_le_divConst_self` / 引理 `one_le_divConst_self`

English:
lemma one_le_divConst_self
  given: (hA : A.Nonempty)
  statement: 1 <= δₘ[A]
  proof: one_le_divConst hA hA

@[to_additive]

中文:
引理 one_le_divConst_self
  条件: (hA : A.Nonempty)
  结论: 1 <= δₘ[A]
  证明: one_le_divConst hA hA

@[to_additive]

Depends on / 依赖: one_le_divConst
-/
lemma one_le_divConst_self (hA : A.Nonempty) : 1 <= δₘ[A] := one_le_divConst hA hA

@[to_additive]
/--
lemma `mulConst_le_card` / 引理 `mulConst_le_card`

English:
lemma mulConst_le_card
  statement: σₘ[A, B] <= #B
  proof: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [mulConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_mul_le

@[to_additive]

中文:
引理 mulConst_le_card
  结论: σₘ[A, B] <= #B
  证明: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [mulConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_mul_le

@[to_additive]

Depends on / 依赖: A.eq_empty_or_nonempty, card_mul_le, eq_empty_or_nonempty, mod_cast, mulConst
-/
lemma mulConst_le_card : σₘ[A, B] <= #B := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [mulConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_mul_le

@[to_additive]
/--
lemma `divConst_le_card` / 引理 `divConst_le_card`

English:
lemma divConst_le_card
  statement: δₘ[A, B] <= #B
  proof: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [divConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_div_le

中文:
引理 divConst_le_card
  结论: δₘ[A, B] <= #B
  证明: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [divConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_div_le

Depends on / 依赖: A.eq_empty_or_nonempty, card_div_le, divConst, eq_empty_or_nonempty, mod_cast
-/
lemma divConst_le_card : δₘ[A, B] <= #B := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [divConst]; rw [div_le_iff₀' (by positivity)]
  exact mod_cast card_div_le

section Fintype
variable [Fintype G]

/-- Dense sets have small doubling. -/
@[to_additive addConst_le_inv_dens /-- Dense sets have small doubling. -/]
/--
lemma `mulConst_le_inv_dens` / 引理 `mulConst_le_inv_dens`

English:
lemma mulConst_le_inv_dens
  statement: σₘ[A, B] <= A.dens⁻¹
  proof: by
  rw [dens]; rw [inv_div]; rw [mulConst]; gcongr; exact card_le_univ _

中文:
引理 mulConst_le_inv_dens
  结论: σₘ[A, B] <= A.dens⁻¹
  证明: by
  rw [dens]; rw [inv_div]; rw [mulConst]; gcongr; exact card_le_univ _

Depends on / 依赖: card_le_univ, inv_div, mulConst
-/
lemma mulConst_le_inv_dens : σₘ[A, B] <= A.dens⁻¹ := by
  rw [dens]; rw [inv_div]; rw [mulConst]; gcongr; exact card_le_univ _

/-- Dense sets have small difference constant. -/
@[to_additive subConst_le_inv_dens /-- Dense sets have small difference constant. -/]
/--
lemma `divConst_le_inv_dens` / 引理 `divConst_le_inv_dens`

English:
lemma divConst_le_inv_dens
  statement: δₘ[A, B] <= A.dens⁻¹
  proof: by
  rw [dens]; rw [inv_div]; rw [divConst]; gcongr; exact card_le_univ _

中文:
引理 divConst_le_inv_dens
  结论: δₘ[A, B] <= A.dens⁻¹
  证明: by
  rw [dens]; rw [inv_div]; rw [divConst]; gcongr; exact card_le_univ _

Depends on / 依赖: card_le_univ, divConst, inv_div
-/
lemma divConst_le_inv_dens : δₘ[A, B] <= A.dens⁻¹ := by
  rw [dens]; rw [inv_div]; rw [divConst]; gcongr; exact card_le_univ _

end Fintype

variable {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]

@[to_additive (dont_translate := 𝕜)]
/--
lemma `cast_mulConst` / 引理 `cast_mulConst`

English:
lemma cast_mulConst
  given: (A B : Finset G)
  statement: (σₘ[A, B] : 𝕜) = #(A * B) / #A
  proof: by simp [mulConst]

@[to_additive (dont_translate := 𝕜)]

中文:
引理 cast_mulConst
  条件: (A B : Finset G)
  结论: (σₘ[A, B] : 𝕜) = #(A * B) / #A
  证明: by simp [mulConst]

@[to_additive (dont_translate := 𝕜)]

Depends on / 依赖: mulConst
-/
lemma cast_mulConst (A B : Finset G) : (σₘ[A, B] : 𝕜) = #(A * B) / #A := by simp [mulConst]

@[to_additive (dont_translate := 𝕜)]
/--
lemma `cast_divConst` / 引理 `cast_divConst`

English:
lemma cast_divConst
  given: (A B : Finset G)
  statement: (δₘ[A, B] : 𝕜) = #(A / B) / #A
  proof: by simp [divConst]

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_addConst_mul_card]

中文:
引理 cast_divConst
  条件: (A B : Finset G)
  结论: (δₘ[A, B] : 𝕜) = #(A / B) / #A
  证明: by simp [divConst]

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_addConst_mul_card]

Depends on / 依赖: divConst
-/
lemma cast_divConst (A B : Finset G) : (δₘ[A, B] : 𝕜) = #(A / B) / #A := by simp [divConst]

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_addConst_mul_card]
/--
lemma `cast_mulConst_mul_card` / 引理 `cast_mulConst_mul_card`

English:
lemma cast_mulConst_mul_card
  given: (A B : Finset G)
  statement: (σₘ[A, B] * #A : 𝕜) = #(A * B)
  proof: by
  norm_cast; exact mulConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_subConst_mul_card]

中文:
引理 cast_mulConst_mul_card
  条件: (A B : Finset G)
  结论: (σₘ[A, B] * #A : 𝕜) = #(A * B)
  证明: by
  norm_cast; exact mulConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_subConst_mul_card]

Depends on / 依赖: mulConst_mul_card
-/
lemma cast_mulConst_mul_card (A B : Finset G) : (σₘ[A, B] * #A : 𝕜) = #(A * B) := by
  norm_cast; exact mulConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_subConst_mul_card]
/--
lemma `cast_divConst_mul_card` / 引理 `cast_divConst_mul_card`

English:
lemma cast_divConst_mul_card
  given: (A B : Finset G)
  statement: (δₘ[A, B] * #A : 𝕜) = #(A / B)
  proof: by
  norm_cast; exact divConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_addConst]

中文:
引理 cast_divConst_mul_card
  条件: (A B : Finset G)
  结论: (δₘ[A, B] * #A : 𝕜) = #(A / B)
  证明: by
  norm_cast; exact divConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_addConst]

Depends on / 依赖: divConst_mul_card
-/
lemma cast_divConst_mul_card (A B : Finset G) : (δₘ[A, B] * #A : 𝕜) = #(A / B) := by
  norm_cast; exact divConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_addConst]
/--
lemma `card_mul_cast_mulConst` / 引理 `card_mul_cast_mulConst`

English:
lemma card_mul_cast_mulConst
  given: (A B : Finset G)
  statement: (#A * σₘ[A, B] : 𝕜) = #(A * B)
  proof: by
  norm_cast; exact card_mul_mulConst _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_subConst]

中文:
引理 card_mul_cast_mulConst
  条件: (A B : Finset G)
  结论: (#A * σₘ[A, B] : 𝕜) = #(A * B)
  证明: by
  norm_cast; exact card_mul_mulConst _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_subConst]

Depends on / 依赖: card_mul_mulConst
-/
lemma card_mul_cast_mulConst (A B : Finset G) : (#A * σₘ[A, B] : 𝕜) = #(A * B) := by
  norm_cast; exact card_mul_mulConst _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_subConst]
/--
lemma `card_mul_cast_divConst` / 引理 `card_mul_cast_divConst`

English:
lemma card_mul_cast_divConst
  given: (A B : Finset G)
  statement: (#A * δₘ[A, B] : 𝕜) = #(A / B)
  proof: by
  norm_cast; exact card_mul_divConst _ _

中文:
引理 card_mul_cast_divConst
  条件: (A B : Finset G)
  结论: (#A * δₘ[A, B] : 𝕜) = #(A / B)
  证明: by
  norm_cast; exact card_mul_divConst _ _

Depends on / 依赖: card_mul_divConst
-/
lemma card_mul_cast_divConst (A B : Finset G) : (#A * δₘ[A, B] : 𝕜) = #(A / B) := by
  norm_cast; exact card_mul_divConst _ _

/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
/--
lemma `divConst_le_mulConst_sq` / 引理 `divConst_le_mulConst_sq`

English:
lemma divConst_le_mulConst_sq
  statement: δₘ[A] <= σₘ[A] ^ 2
  proof: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A / A) * (#A : Rat>=0) := by rw [← mul_assoc, divConst_mul_card]
    _ <= #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul

中文:
引理 divConst_le_mulConst_sq
  结论: δₘ[A] <= σₘ[A] ^ 2
  证明: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A / A) * (#A : Rat>=0) := by rw [← mul_assoc, divConst_mul_card]
    _ <= #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul

Depends on / 依赖: A.eq_empty_or_nonempty, divConst_mul_card, eq_empty_or_nonempty, le_of_mul_le_mul_right, mulConst_mul_card, mul_assoc, ruzsa_triangle_inequality_div_mul_mul
-/
lemma divConst_le_mulConst_sq : δₘ[A] <= σₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A / A) * (#A : Rat>=0) := by rw [← mul_assoc, divConst_mul_card]
    _ <= #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul_mul ..
    _ = _ := by rw [← mulConst_mul_card]; ring

end Group

open scoped Combinatorics.Additive

section CommGroup
variable {G : Type*} [CommGroup G] [DecidableEq G] {A B : Finset G}

@[to_additive (attr := simp)]
/--
lemma `mulConst_inv_left` / 引理 `mulConst_inv_left`

English:
lemma mulConst_inv_left
  given: (A B : Finset G)
  statement: σₘ[A⁻¹, B] = δₘ[A, B]
  proof: by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_mul_eq_div]

@[to_additive (attr := simp)]

中文:
引理 mulConst_inv_left
  条件: (A B : Finset G)
  结论: σₘ[A⁻¹, B] = δₘ[A, B]
  证明: by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_mul_eq_div]

@[to_additive (attr := simp)]

Depends on / 依赖: card_inv, divConst, inv_inv, inv_mul_eq_div, mulConst, mul_inv_rev
-/
lemma mulConst_inv_left (A B : Finset G) : σₘ[A⁻¹, B] = δₘ[A, B] := by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_mul_eq_div]

@[to_additive (attr := simp)]
/--
lemma `divConst_inv_left` / 引理 `divConst_inv_left`

English:
lemma divConst_inv_left
  given: (A B : Finset G)
  statement: δₘ[A⁻¹, B] = σₘ[A, B]
  proof: by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [inv_div]; rw [div_inv_eq_mul]; rw [mul_comm]

中文:
引理 divConst_inv_left
  条件: (A B : Finset G)
  结论: δₘ[A⁻¹, B] = σₘ[A, B]
  证明: by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [inv_div]; rw [div_inv_eq_mul]; rw [mul_comm]

Depends on / 依赖: card_inv, divConst, div_inv_eq_mul, inv_div, mulConst, mul_comm
-/
lemma divConst_inv_left (A B : Finset G) : δₘ[A⁻¹, B] = σₘ[A, B] := by
  rw [mulConst]; rw [divConst]; rw [card_inv]; rw [← card_inv]; rw [inv_div]; rw [div_inv_eq_mul]; rw [mul_comm]

/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
/--
lemma `mulConst_le_divConst_sq` / 引理 `mulConst_le_divConst_sq`

English:
lemma mulConst_le_divConst_sq
  statement: σₘ[A] <= δₘ[A] ^ 2
  proof: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A * A) * (#A : Rat>=0) := by rw [← mul_assoc, mulConst_mul_card]
    _ <= #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div

中文:
引理 mulConst_le_divConst_sq
  结论: σₘ[A] <= δₘ[A] ^ 2
  证明: by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A * A) * (#A : Rat>=0) := by rw [← mul_assoc, mulConst_mul_card]
    _ <= #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div

Depends on / 依赖: A.eq_empty_or_nonempty, divConst_mul_card, eq_empty_or_nonempty, le_of_mul_le_mul_right, mulConst_mul_card, mul_assoc, ruzsa_triangle_inequality_mul_div_div
-/
lemma mulConst_le_divConst_sq : σₘ[A] <= δₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A * #A)
  calc
    _ = #(A * A) * (#A : Rat>=0) := by rw [← mul_assoc, mulConst_mul_card]
    _ <= #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div_div ..
    _ = _ := by rw [← divConst_mul_card]; ring

end CommGroup
end Finset
