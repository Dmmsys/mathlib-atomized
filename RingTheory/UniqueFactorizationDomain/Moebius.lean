/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# The Moebius function on a unique factorization monoid

We define the Moebius function on a unique factorization monoid.

## Main definitions

* `UniqueFactorizationMonoid.moebius`: The Moebius function on a unique factorization monoid,
  defined to be `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise.

## Main statements

* `IsRelPrime.moebius_mul`: The Moebius function is a multiplicative function.
-/

@[expose] public section

namespace UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a b : α}

/--
Definition of `moebius` / `moebius` 的定义

English:
definition moebius
  signature: (a : α)
  body: open scoped Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

中文:
定义 moebius
  签名: (a : α)
  定义体: open scoped Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

Depends on / 依赖: Classical, Squarefree, factors, scoped
-/
noncomputable def moebius (a : α) : Int :=
  open scoped Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

-- Todo: prove `Int.moebius_eq` as well.
/--
theorem `_root_.Nat.moebius_eq` / 定理 `_root_.Nat.moebius_eq`

English:
theorem _root_.Nat.moebius_eq
  given: (n : Nat)
  statement: moebius n = ArithmeticFunction.moebius n
  proof: by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]

@[simp]

中文:
定理 _root_.自然数.moebius_eq
  条件: (n : 自然数)
  结论: moebius n = ArithmeticFunction.moebius n
  证明: by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]

@[simp]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardFactors_apply, Nat.factors_eq, cardFactors_apply, factors_eq, moebius
-/
theorem _root_.Nat.moebius_eq (n : Nat) : moebius n = ArithmeticFunction.moebius n := by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]

@[simp]
/--
theorem `_root_.Squarefree.moebius_eq` / 定理 `_root_.Squarefree.moebius_eq`

English:
theorem _root_.Squarefree.moebius_eq
  given: (ha : Squarefree a)
  statement: moebius a = (-1) ^ (factors a).card
  proof: if_pos ha

@[simp]

中文:
定理 _root_.Squarefree.moebius_eq
  条件: (ha : Squarefree a)
  结论: moebius a = (-1) ^ (factors a).card
  证明: if_pos ha

@[simp]

Depends on / 依赖: if_pos
-/
theorem _root_.Squarefree.moebius_eq (ha : Squarefree a) : moebius a = (-1) ^ (factors a).card :=
  if_pos ha

@[simp]
/--
theorem `moebius_of_not_squarefree` / 定理 `moebius_of_not_squarefree`

English:
theorem moebius_of_not_squarefree
  given: (ha : ¬ Squarefree a)
  statement: moebius a = 0
  proof: if_neg ha

中文:
定理 moebius_of_not_squarefree
  条件: (ha : ¬ Squarefree a)
  结论: moebius a = 0
  证明: if_neg ha

Depends on / 依赖: if_neg
-/
theorem moebius_of_not_squarefree (ha : ¬ Squarefree a) : moebius a = 0 :=
  if_neg ha

/--
theorem `moebius_zero` / 定理 `moebius_zero`

English:
theorem moebius_zero
  given: [Nontrivial α]
  statement: moebius (0 : α) = 0
  proof: by
  simp

中文:
定理 moebius_zero
  条件: [非平凡 α]
  结论: moebius (0 : α) = 0
  证明: by
  simp
-/
theorem moebius_zero [Nontrivial α] : moebius (0 : α) = 0 := by
  simp

/--
theorem `moebius_one` / 定理 `moebius_one`

English:
theorem moebius_one
  statement: moebius (1 : α) = 1
  proof: by
  simp

中文:
定理 moebius_one
  结论: moebius (1 : α) = 1
  证明: by
  simp
-/
theorem moebius_one : moebius (1 : α) = 1 := by
  simp

/--
theorem `_root_.Associated.moebius_eq` / 定理 `_root_.Associated.moebius_eq`

English:
theorem _root_.Associated.moebius_eq
  given: (h : Associated a b)
  statement: moebius a = moebius b
  proof: by
  rw [moebius]; rw [moebius]; rw [h.squarefree_iff]; rw [h.card_factors_eq]

中文:
定理 _root_.Associated.moebius_eq
  条件: (h : Associated a b)
  结论: moebius a = moebius b
  证明: by
  rw [moebius]; rw [moebius]; rw [h.squarefree_iff]; rw [h.card_factors_eq]

Depends on / 依赖: card_factors_eq, h.card_factors_eq, h.squarefree_iff, moebius, squarefree_iff
-/
theorem _root_.Associated.moebius_eq (h : Associated a b) : moebius a = moebius b := by
  rw [moebius]; rw [moebius]; rw [h.squarefree_iff]; rw [h.card_factors_eq]

/--
theorem `_root_.IsUnit.moebius_eq` / 定理 `_root_.IsUnit.moebius_eq`

English:
theorem _root_.IsUnit.moebius_eq
  given: (ha : IsUnit a)
  statement: moebius a = 1
  proof: by
  rw [(associated_one_iff_isUnit.mpr ha).moebius_eq]; rw [moebius_one]

中文:
定理 _root_.是单位.moebius_eq
  条件: (ha : 是单位 a)
  结论: moebius a = 1
  证明: by
  rw [(associated_one_iff_isUnit.mpr ha).moebius_eq]; rw [moebius_one]

Depends on / 依赖: associated_one_iff_isUnit, associated_one_iff_isUnit.mpr, moebius_eq, moebius_one
-/
theorem _root_.IsUnit.moebius_eq (ha : IsUnit a) : moebius a = 1 := by
  rw [(associated_one_iff_isUnit.mpr ha).moebius_eq]; rw [moebius_one]

/--
theorem `_root_.Irreducible.moebius_eq` / 定理 `_root_.Irreducible.moebius_eq`

English:
theorem _root_.Irreducible.moebius_eq
  given: (ha : Irreducible a)
  statement: moebius a = -1
  proof: by
  rw [ha.squarefree.moebius_eq]; rw [card_factors_of_irreducible ha]; rw [pow_one]

中文:
定理 _root_.不可约.moebius_eq
  条件: (ha : 不可约 a)
  结论: moebius a = -1
  证明: by
  rw [ha.squarefree.moebius_eq]; rw [card_factors_of_irreducible ha]; rw [pow_one]

Depends on / 依赖: card_factors_of_irreducible, ha.squarefree.moebius_eq, moebius_eq, pow_one, squarefree
-/
theorem _root_.Irreducible.moebius_eq (ha : Irreducible a) : moebius a = -1 := by
  rw [ha.squarefree.moebius_eq]; rw [card_factors_of_irreducible ha]; rw [pow_one]

/--
theorem `_root_.IsRelPrime.moebius_mul` / 定理 `_root_.IsRelPrime.moebius_mul`

English:
theorem _root_.IsRelPrime.moebius_mul
  given: (h : IsRelPrime a b)
  proof: by
  rcases subsingleton_or_nontrivial α
  · rw [Subsingleton.elim a 1, moebius_one, one_mul, one_mul]
  by_cases ha : Squarefree a; swap
  · simp [ha, mt Squarefree.of_mul_left ha]
  by_cases hb : Squarefree b; swap
  · simp [hb, mt Squarefree.of_mul_right hb]
  have hab : Squarefree (a * b) := squ

中文:
定理 _root_.IsRelPrime.moebius_mul
  条件: (h : IsRelPrime a b)
  证明: by
  rcases subsingleton_or_nontrivial α
  · rw [Subsingleton.elim a 1, moebius_one, one_mul, one_mul]
  by_cases ha : Squarefree a; swap
  · simp [ha, mt Squarefree.of_mul_left ha]
  by_cases hb : Squarefree b; swap
  · simp [hb, mt Squarefree.of_mul_right hb]
  have hab : Squarefree (a * b) := squ

Depends on / 依赖: Multiset, Multiset.card_add, Multiset.card_eq_card_of_rel, Squarefree, Squarefree.of_mul_left, Squarefree.of_mul_right, Subsingleton, Subsingleton.elim, card_add, card_eq_card_of_rel, factors_mul, ha.moebius_eq, ha.ne_zero, hab.moebius_eq, hb.moebius_eq, hb.ne_zero, moebius_eq, moebius_one, ne_zero, of_mul_left
-/
theorem _root_.IsRelPrime.moebius_mul (h : IsRelPrime a b) :
    moebius (a * b) = moebius a * moebius b := by
  rcases subsingleton_or_nontrivial α
  · rw [Subsingleton.elim a 1, moebius_one, one_mul, one_mul]
  by_cases ha : Squarefree a; swap
  · simp [ha, mt Squarefree.of_mul_left ha]
  by_cases hb : Squarefree b; swap
  · simp [hb, mt Squarefree.of_mul_right hb]
  have hab : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨h, ha, hb⟩
  rw [hab.moebius_eq]; rw [Multiset.card_eq_card_of_rel (factors_mul ha.ne_zero hb.ne_zero)]; rw [Multiset.card_add]; rw [pow_add]; rw [ha.moebius_eq]; rw [hb.moebius_eq]

end UniqueFactorizationMonoid
