/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Duality

/-!
# Orthogonality relations for Dirichlet characters

Let `n` be a positive natural number. The main result of this file is
`DirichletCharacter.sum_char_inv_mul_char_eq`, which says that when `a : ZMod n` is a unit
and `b : ZMod n`, then the sum `∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b` vanishes
when `a ≠ b` and has the value `n.totient` otherwise. This requires `R` to have
enough roots of unity (e.g., `R` could be an algebraically closed field of characteristic zero).
-/

public section

namespace DirichletCharacter

-- This is needed to be able to write down sums over characters.
/--
Instance `fintype` / 实例 `fintype`

English:
instance fintype
  signature: {R : Type*} [CommRing R] [IsDomain R] {n : Nat}
  body: .ofFinite _

中文:
实例 fintype
  签名: {R : 类型} [交换环 R] [是整环 R] {n : 自然数}
  定义体: .ofFinite _

Depends on / 依赖: ofFinite
-/
noncomputable instance fintype {R : Type*} [CommRing R] [IsDomain R] {n : Nat} :
    Fintype (DirichletCharacter R n) := .ofFinite _

variable (R : Type*) [CommRing R] (n : Nat) [NeZero n]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/--
lemma `mulEquiv_units` / 引理 `mulEquiv_units`

English:
lemma mulEquiv_units
  statement: Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ)
  proof: MulChar.mulEquiv_units ..

中文:
引理 mulEquiv_units
  结论: 非空 (DirichletCharacter R n ≃* (ZMod n)ˣ)
  证明: MulChar.mulEquiv_units ..

Depends on / 依赖: MulChar, MulChar.mulEquiv_units, mulEquiv_units
-/
lemma mulEquiv_units : Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ) :=
  MulChar.mulEquiv_units ..

/--
lemma `card_eq_totient_of_hasEnoughRootsOfUnity` / 引理 `card_eq_totient_of_hasEnoughRootsOfUnity`

English:
lemma card_eq_totient_of_hasEnoughRootsOfUnity
  proof: by
  rw [← ZMod.card_units_eq_totient n]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

中文:
引理 card_eq_totient_of_hasEnoughRootsOfUnity
  证明: by
  rw [← ZMod.card_units_eq_totient n]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

Depends on / 依赖: Nat.card_congr, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, card_congr, card_eq_fintype_card, card_units_eq_totient, mulEquiv_units, some.toEquiv, toEquiv
-/
lemma card_eq_totient_of_hasEnoughRootsOfUnity :
    Nat.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

variable {n}

/--
theorem `exists_apply_ne_one_of_hasEnoughRootsOfUnity` / 定理 `exists_apply_ne_one_of_hasEnoughRootsOfUnity`

English:
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity
  given: [Nontrivial R] ⦃a
  statement: ZMod n⦄ (ha : a != 1) :
  proof: MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

中文:
定理 存在_apply_ne_one_of_hasEnoughRootsOfUnity
  条件: [非平凡 R] ⦃a
  结论: ZMod n⦄ (ha : a != 1) :
  证明: MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

Depends on / 依赖: MulChar, MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity, exists_apply_ne_one_of_hasEnoughRootsOfUnity
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] ⦃a : ZMod n⦄ (ha : a != 1) :
    exists χ : DirichletCharacter R n, χ a != 1 :=
  MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

variable [IsDomain R]

/--
theorem `sum_characters_eq_zero` / 定理 `sum_characters_eq_zero`

English:
theorem sum_characters_eq_zero
  given: ⦃a
  statement: ZMod n⦄ (ha : a != 1) :
  proof: by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

中文:
定理 sum_characters_eq_zero
  条件: ⦃a
  结论: ZMod n⦄ (ha : a != 1) :
  证明: by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

Depends on / 依赖: Finset, Finset.mul_sum, Fintype, Fintype.sum_bijective, Group.mulLeft_bijective, MulChar, MulChar.mul_apply, eq_zero_of_mul_eq_self_left, exists_apply_ne_one_of_hasEnoughRootsOfUnity, mulLeft_bijective, mul_apply, mul_sum, sum_bijective
-/
theorem sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a != 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

/--
theorem `sum_characters_eq` / 定理 `sum_characters_eq`

English:
theorem sum_characters_eq
  given: (a : ZMod n)
  proof: by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
using congrArg Nat.cast card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

中文:
定理 sum_characters_eq
  条件: (a : ZMod n)
  证明: by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
using congrArg Nat.cast card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Nat.card_eq_fintype_card, Nat.cast, card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity, card_univ, map_one, mul_one, nsmul_eq_mul, split_ifs, sum_characters_eq_zero, sum_const
-/
theorem sum_characters_eq (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
using congrArg Nat.cast card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

/--
theorem `sum_char_inv_mul_char_eq` / 定理 `sum_char_inv_mul_char_eq`

English:
theorem sum_char_inv_mul_char_eq
  given: {a : ZMod n} (ha : IsUnit a) (b : ZMod n)
  proof: by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

中文:
定理 sum_char_inv_mul_char_eq
  条件: {a : ZMod n} (ha : 是单位 a) (b : ZMod n)
  证明: by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

Depends on / 依赖: ZMod.inv_mul_eq_one_of_isUnit, inv_mul_eq_one_of_isUnit, map_mul, sum_characters_eq
-/
theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0 := by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

end DirichletCharacter
