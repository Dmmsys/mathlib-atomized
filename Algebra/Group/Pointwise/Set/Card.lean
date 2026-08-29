/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Data.Set.Card

/-!
# Cardinalities of pointwise operations on sets
-/

public section

assert_not_exists Field

open scoped Cardinal Pointwise

namespace Set
variable {G M α : Type*}

section Mul
variable [Mul M] {s t : Set M}

@[to_additive]
/--
lemma `_root_.Cardinal.mk_mul_le` / 引理 `_root_.Cardinal.mk_mul_le`

English:
lemma _root_.Cardinal.mk_mul_le
  statement: #(s * t) <= #s * #t
  proof: by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

中文:
引理 _root_.基数.mk_mul_le
  结论: #(s * t) <= #s * #t
  证明: by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

Depends on / 依赖: Cardinal, Cardinal.mk_image2_le, image2_mul, mk_image2_le
-/
lemma _root_.Cardinal.mk_mul_le : #(s * t) <= #s * #t := by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

variable [IsCancelMul M]

@[to_additive]
/--
lemma `natCard_mul_le` / 引理 `natCard_mul_le`

English:
lemma natCard_mul_le
  statement: Nat.card (s * t) <= Nat.card s * Nat.card t
  proof: by
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  simp only [Nat.card, ← Cardinal.toNat_mul]
  refine Cardinal.toNat_le_toNat Cardinal.mk_mul_le ?_
  aesop (add simp [Cardinal.mul_lt_aleph0_iff, finite_mul])

中文:
引理 natCard_mul_le
  结论: 自然数.card (s * t) <= 自然数.card s * 自然数.card t
  证明: by
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  simp only [Nat.card, ← Cardinal.toNat_mul]
  refine Cardinal.toNat_le_toNat Cardinal.mk_mul_le ?_
  aesop (add simp [Cardinal.mul_lt_aleph0_iff, finite_mul])

Depends on / 依赖: Cardinal, Cardinal.mk_mul_le, Cardinal.mul_lt_aleph0_iff, Cardinal.toNat_le_toNat, Cardinal.toNat_mul, Infinite, Nat.card, Set.Infinite.card_eq_zero, card_eq_zero, finite_mul, infinite_or_finite, mk_mul_le, mul_lt_aleph0_iff, toNat_le_toNat, toNat_mul
-/
lemma natCard_mul_le : Nat.card (s * t) <= Nat.card s * Nat.card t := by
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  simp only [Nat.card, ← Cardinal.toNat_mul]
  refine Cardinal.toNat_le_toNat Cardinal.mk_mul_le ?_
  aesop (add simp [Cardinal.mul_lt_aleph0_iff, finite_mul])

end Mul

section InvolutiveInv
variable [InvolutiveInv G]

@[to_additive (attr := simp)]
/--
lemma `_root_.Cardinal.mk_inv` / 引理 `_root_.Cardinal.mk_inv`

English:
lemma _root_.Cardinal.mk_inv
  given: (s : Set G)
  statement: #↥(s⁻¹) = #s
  proof: by
  rw [← image_inv_eq_inv]; rw [Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]

中文:
引理 _root_.基数.mk_inv
  条件: (s : 集合 G)
  结论: #↥(s⁻¹) = #s
  证明: by
  rw [← image_inv_eq_inv]; rw [Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]

Depends on / 依赖: Cardinal, Cardinal.mk_image_eq_of_injOn, image_inv_eq_inv, inv_injective, inv_injective.injOn, mk_image_eq_of_injOn
-/
lemma _root_.Cardinal.mk_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv_eq_inv]; rw [Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]
/--
lemma `encard_inv` / 引理 `encard_inv`

English:
lemma encard_inv
  given: (s : Set G)
  statement: s⁻¹.encard = s.encard
  proof: by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]

中文:
引理 encard_inv
  条件: (s : 集合 G)
  结论: s⁻¹.encard = s.encard
  证明: by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]

Depends on / 依赖: toENat_cardinalMk
-/
lemma encard_inv (s : Set G) : s⁻¹.encard = s.encard := by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]
/--
lemma `ncard_inv` / 引理 `ncard_inv`

English:
lemma ncard_inv
  given: (s : Set G)
  statement: s⁻¹.ncard = s.ncard
  proof: by simp [ncard]

@[to_additive]

中文:
引理 ncard_inv
  条件: (s : 集合 G)
  结论: s⁻¹.ncard = s.ncard
  证明: by simp [ncard]

@[to_additive]
-/
lemma ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard := by simp [ncard]

@[to_additive]
/--
lemma `natCard_inv` / 引理 `natCard_inv`

English:
lemma natCard_inv
  given: (s : Set G)
  statement: Nat.card ↥(s⁻¹) = Nat.card s
  proof: by simp

中文:
引理 natCard_inv
  条件: (s : 集合 G)
  结论: 自然数.card ↥(s⁻¹) = 自然数.card s
  证明: by simp
-/
lemma natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by simp

end InvolutiveInv

section DivInvMonoid
variable [DivInvMonoid M] {s t : Set M}

@[to_additive]
/--
lemma `_root_.Cardinal.mk_div_le` / 引理 `_root_.Cardinal.mk_div_le`

English:
lemma _root_.Cardinal.mk_div_le
  statement: #(s / t) <= #s * #t
  proof: by
  rw [← image2_div]; exact Cardinal.mk_image2_le

中文:
引理 _root_.基数.mk_div_le
  结论: #(s / t) <= #s * #t
  证明: by
  rw [← image2_div]; exact Cardinal.mk_image2_le

Depends on / 依赖: Cardinal, Cardinal.mk_image2_le, image2_div, mk_image2_le
-/
lemma _root_.Cardinal.mk_div_le : #(s / t) <= #s * #t := by
  rw [← image2_div]; exact Cardinal.mk_image2_le

end DivInvMonoid

section Group
variable [Group G] {s t : Set G}

@[to_additive]
/--
lemma `natCard_div_le` / 引理 `natCard_div_le`

English:
lemma natCard_div_le
  statement: Nat.card (s / t) <= Nat.card s * Nat.card t
  proof: by
  rw [div_eq_mul_inv]; rw [← natCard_inv t]; exact natCard_mul_le

中文:
引理 natCard_div_le
  结论: 自然数.card (s / t) <= 自然数.card s * 自然数.card t
  证明: by
  rw [div_eq_mul_inv]; rw [← natCard_inv t]; exact natCard_mul_le

Depends on / 依赖: div_eq_mul_inv, natCard_inv, natCard_mul_le
-/
lemma natCard_div_le : Nat.card (s / t) <= Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv]; rw [← natCard_inv t]; exact natCard_mul_le

variable [MulAction G α]

@[to_additive (attr := simp)]
/--
lemma `_root_.Cardinal.mk_smul_set` / 引理 `_root_.Cardinal.mk_smul_set`

English:
lemma _root_.Cardinal.mk_smul_set
  given: (a : G) (s : Set α)
  statement: #↥(a • s) = #s
  proof: Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]

中文:
引理 _root_.基数.mk_smul_set
  条件: (a : G) (s : 集合 α)
  结论: #↥(a • s) = #s
  证明: Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]

Depends on / 依赖: Cardinal, Cardinal.mk_image_eq_of_injOn, MulAction, MulAction.injective, injective, mk_image_eq_of_injOn
-/
lemma _root_.Cardinal.mk_smul_set (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]
/--
lemma `encard_smul_set` / 引理 `encard_smul_set`

English:
lemma encard_smul_set
  given: (a : G) (s : Set α)
  statement: (a • s).encard = s.encard
  proof: by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]

中文:
引理 encard_smul_set
  条件: (a : G) (s : 集合 α)
  结论: (a • s).encard = s.encard
  证明: by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]

Depends on / 依赖: toENat_cardinalMk
-/
lemma encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard := by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]
/--
lemma `ncard_smul_set` / 引理 `ncard_smul_set`

English:
lemma ncard_smul_set
  given: (a : G) (s : Set α)
  statement: (a • s).ncard = s.ncard
  proof: by simp [ncard]

@[to_additive]

中文:
引理 ncard_smul_set
  条件: (a : G) (s : 集合 α)
  结论: (a • s).ncard = s.ncard
  证明: by simp [ncard]

@[to_additive]
-/
lemma ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard := by simp [ncard]

@[to_additive]
/--
lemma `natCard_smul_set` / 引理 `natCard_smul_set`

English:
lemma natCard_smul_set
  given: (a : G) (s : Set α)
  statement: Nat.card ↥(a • s) = Nat.card s
  proof: by
  simp

中文:
引理 natCard_smul_set
  条件: (a : G) (s : 集合 α)
  结论: 自然数.card ↥(a • s) = 自然数.card s
  证明: by
  simp
-/
lemma natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s := by
  simp

end Group
end Set
