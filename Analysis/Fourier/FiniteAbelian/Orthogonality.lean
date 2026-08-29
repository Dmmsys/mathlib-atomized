/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.RCLike.Inner

/-!
# Orthogonality of characters of a finite abelian group

This file proves that characters of a finite abelian group are orthogonal, and in particular that
there are at most as many characters as there are elements of the group.
-/

public section

open Finset hiding card
open Fintype (card)
open Function RCLike
open scoped BigOperators ComplexConjugate DirectSum

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section Semifield
variable [Fintype G] [Semifield R] [CharZero R] {ψ : AddChar G R}

/--
lemma `expect_eq_ite` / 引理 `expect_eq_ite`

English:
lemma expect_eq_ite
  given: (ψ : AddChar G R)
  statement: 𝔼 a, ψ a = if ψ = 0 then 1 else 0
  proof: by
  simp [Fintype.expect_eq_sum_div_card, sum_eq_ite, ite_div]

中文:
引理 expect_eq_ite
  条件: (ψ : 加法特征 G R)
  结论: 𝔼 a, ψ a = if ψ = 0 then 1 else 0
  证明: by
  simp [Fintype.expect_eq_sum_div_card, sum_eq_ite, ite_div]

Depends on / 依赖: Fintype, Fintype.expect_eq_sum_div_card, NormedGroup, SetLike, SubgroupClass, expect_eq_sum_div_card, ite_div, normedGroup, sum_eq_ite
-/
lemma expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0 := by
  simp [Fintype.expect_eq_sum_div_card, sum_eq_ite, ite_div]

/--
lemma `expect_eq_zero_iff_ne_zero` / 引理 `expect_eq_zero_iff_ne_zero`

English:
lemma expect_eq_zero_iff_ne_zero
  statement: 𝔼 x, ψ x = 0 ↔ ψ != 0
  proof: by
  rw [expect_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

中文:
引理 expect_eq_zero_iff_ne_zero
  结论: 𝔼 x, ψ x = 0 ↔ ψ != 0
  证明: by
  rw [expect_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

Depends on / 依赖: NormedCommGroup, SetLike, expect_eq_ite, ite_eq_right_iff, normedCommGroup, one_ne_zero, one_ne_zero.ite_eq_right_iff
-/
lemma expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ != 0 := by
  rw [expect_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

/--
lemma `expect_ne_zero_iff_eq_zero` / 引理 `expect_ne_zero_iff_eq_zero`

English:
lemma expect_ne_zero_iff_eq_zero
  statement: 𝔼 x, ψ x != 0 ↔ ψ = 0
  proof: expect_eq_zero_iff_ne_zero.not_left

中文:
引理 expect_ne_zero_iff_eq_zero
  结论: 𝔼 x, ψ x != 0 ↔ ψ = 0
  证明: expect_eq_zero_iff_ne_zero.not_left

Depends on / 依赖: expect_eq_zero_iff_ne_zero, expect_eq_zero_iff_ne_zero.not_left, not_left
-/
lemma expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x != 0 ↔ ψ = 0 := expect_eq_zero_iff_ne_zero.not_left

end Semifield

section RCLike
variable [RCLike R] [Fintype G]

/--
lemma `wInner_cWeight_self` / 引理 `wInner_cWeight_self`

English:
lemma wInner_cWeight_self
  given: (ψ : AddChar G R)
  statement: ⟪(ψ : G -> R), ψ⟫ₙ_[R] = 1
  proof: by
  simp [wInner_cWeight_eq_expect, ψ.norm_apply]

中文:
引理 wInner_cWeight_self
  条件: (ψ : 加法特征 G R)
  结论: ⟪(ψ : G -> R), ψ⟫ₙ_[R] = 1
  证明: by
  simp [wInner_cWeight_eq_expect, ψ.norm_apply]

Depends on / 依赖: norm_apply, wInner_cWeight_eq_expect
-/
lemma wInner_cWeight_self (ψ : AddChar G R) : ⟪(ψ : G -> R), ψ⟫ₙ_[R] = 1 := by
  simp [wInner_cWeight_eq_expect, ψ.norm_apply]

end RCLike
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

/--
lemma `wInner_cWeight_eq_boole` / 引理 `wInner_cWeight_eq_boole`

English:
lemma wInner_cWeight_eq_boole
  given: [Fintype G] (ψ₁ ψ₂ : AddChar G R)
  proof: by
  split_ifs with h
  · rw [h, wInner_cWeight_self]
  have : ψ₂ * ψ₁⁻¹ != 1 := by rwa [Ne, mul_inv_eq_one, eq_comm]
  simp_rw [wInner_cWeight_eq_expect, RCLike.inner_apply, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using expect_eq_zero_iff_ne_zero.2 this

中文:
引理 wInner_cWeight_eq_boole
  条件: [有限类型 G] (ψ₁ ψ₂ : 加法特征 G R)
  证明: by
  split_ifs with h
  · rw [h, wInner_cWeight_self]
  have : ψ₂ * ψ₁⁻¹ != 1 := by rwa [Ne, mul_inv_eq_one, eq_comm]
  simp_rw [wInner_cWeight_eq_expect, RCLike.inner_apply, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using expect_eq_zero_iff_ne_zero.2 this

Depends on / 依赖: RCLike, RCLike.inner_apply, eq_comm, expect_eq_zero_iff_ne_zero, inner_apply, inv_apply_eq_conj, map_neg_eq_inv, mul_inv_eq_one, simp_rw, split_ifs, wInner_cWeight_eq_expect, wInner_cWeight_self
-/
lemma wInner_cWeight_eq_boole [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0 := by
  split_ifs with h
  · rw [h, wInner_cWeight_self]
  have : ψ₂ * ψ₁⁻¹ != 1 := by rwa [Ne, mul_inv_eq_one, eq_comm]
  simp_rw [wInner_cWeight_eq_expect, RCLike.inner_apply, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using expect_eq_zero_iff_ne_zero.2 this

/--
lemma `wInner_cWeight_eq_zero_iff_ne` / 引理 `wInner_cWeight_eq_zero_iff_ne`

English:
lemma wInner_cWeight_eq_zero_iff_ne
  given: [Fintype G]
  statement: ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ != ψ₂
  proof: by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_right_iff]

中文:
引理 wInner_cWeight_eq_zero_iff_ne
  条件: [有限类型 G]
  结论: ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ != ψ₂
  证明: by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_right_iff]

Depends on / 依赖: ite_eq_right_iff, one_ne_zero, one_ne_zero.ite_eq_right_iff, wInner_cWeight_eq_boole
-/
lemma wInner_cWeight_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ != ψ₂ := by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_right_iff]

/--
lemma `wInner_cWeight_eq_one_iff_eq` / 引理 `wInner_cWeight_eq_one_iff_eq`

English:
lemma wInner_cWeight_eq_one_iff_eq
  given: [Fintype G]
  statement: ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 1 ↔ ψ₁ = ψ₂
  proof: by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_left_iff]

中文:
引理 wInner_cWeight_eq_one_iff_eq
  条件: [有限类型 G]
  结论: ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 1 ↔ ψ₁ = ψ₂
  证明: by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_left_iff]

Depends on / 依赖: ite_eq_left_iff, one_ne_zero, one_ne_zero.ite_eq_left_iff, wInner_cWeight_eq_boole
-/
lemma wInner_cWeight_eq_one_iff_eq [Fintype G] : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 1 ↔ ψ₁ = ψ₂ := by
  rw [wInner_cWeight_eq_boole]; rw [one_ne_zero.ite_eq_left_iff]

variable (G R)

/--
lemma `linearIndependent` / 引理 `linearIndependent`

English:
lemma linearIndependent
  given: [Finite G]
  statement: LinearIndependent R ((⇑) : AddChar G R -> G -> R)
  proof: by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero coe_ne_zero
    fun ψ₁ ψ₂ => wInner_cWeight_eq_zero_iff_ne.2

中文:
引理 linearIndependent
  条件: [有限 G]
  结论: LinearIndependent R ((⇑) : 加法特征 G R -> G -> R)
  证明: by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero coe_ne_zero
    fun ψ₁ ψ₂ => wInner_cWeight_eq_zero_iff_ne.2
-/
protected lemma linearIndependent [Finite G] : LinearIndependent R ((⇑) : AddChar G R -> G -> R) := by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero coe_ne_zero
    fun ψ₁ ψ₂ => wInner_cWeight_eq_zero_iff_ne.2

/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: [Finite G]
  body: @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

中文:
实例 instFintype
  签名: [有限 G]
  定义体: @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

Depends on / 依赖: AddChar, AddChar.linearIndependent, Fintype, Fintype.ofFinite, finite, linearIndependent, ofFinite
-/
noncomputable instance instFintype [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

/--
lemma `card_addChar_le` / 引理 `card_addChar_le`

English:
lemma card_addChar_le
  given: [Fintype G]
  statement: card (AddChar G R) <= card G
  proof: by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

中文:
引理 card_addChar_le
  条件: [有限类型 G]
  结论: card (加法特征 G R) <= card G
  证明: by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank
-/
@[simp] lemma card_addChar_le [Fintype G] : card (AddChar G R) <= card G := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

end RCLike
end AddCommGroup
end AddChar
