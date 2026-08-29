/-
Copyright (c) 2025 Qinchuan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qinchuan Zhang
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Vieta's Formula for polynomial of small degrees.
-/

public section

namespace Polynomial

variable {R T S : Type*}

/--
lemma `eq_quadratic_of_degree_le_two` / 引理 `eq_quadratic_of_degree_le_two`

English:
lemma eq_quadratic_of_degree_le_two
  given: [Semiring R] {p : R[X]} (hp : p.degree <= 2)
  proof: by
  rw [p.as_sum_range_C_mul_X_pow'
    (Nat.lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr hp) (Nat.lt_add_one 2))]
  simp [Finset.sum_range_succ]
  abel

中文:
引理 eq_quadratic_of_degree_le_two
  条件: [半环 R] {p : R[X]} (hp : p.degree <= 2)
  证明: by
  rw [p.as_sum_range_C_mul_X_pow'
    (Nat.lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr hp) (Nat.lt_add_one 2))]
  simp [Finset.sum_range_succ]
  abel

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.lt_add_one, Nat.lt_of_le_of_lt, as_sum_range_C_mul_X_pow, lt_add_one, lt_of_le_of_lt, natDegree_le_iff_degree_le, natDegree_le_iff_degree_le.mpr, p.as_sum_range_C_mul_X_pow, sum_range_succ
-/
lemma eq_quadratic_of_degree_le_two [Semiring R] {p : R[X]} (hp : p.degree <= 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  rw [p.as_sum_range_C_mul_X_pow'
    (Nat.lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr hp) (Nat.lt_add_one 2))]
  simp [Finset.sum_range_succ]
  abel

/--
lemma `eq_neg_mul_add_of_roots_quadratic_eq_pair` / 引理 `eq_neg_mul_add_of_roots_quadratic_eq_pair`

English:
lemma eq_neg_mul_add_of_roots_quadratic_eq_pair
  statement: [CommRing R] [IsDomain R] {a b c x1 x2 : R}
  proof: by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_

中文:
引理 eq_neg_mul_add_of_roots_quadratic_eq_pair
  结论: [交换环 R] [是整环 R] {a b c x1 x2 : R}
  证明: by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_

Depends on / 依赖: Multiset, Multiset.card_pair, add_comm, card_pair, card_roots, coeff_eq_esymm_roots_of_card, convert, hp_natDegree, hp_roots_card, hroots, le_antisymm, leadingCoeff, mul_assoc, natDegree, natDegree_quadratic_le, p.card_roots, p.natDegree, p.roots.card
-/
lemma eq_neg_mul_add_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    b = -a * (x1 + x2) := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by simp [hp_natDegree])

/--
lemma `eq_mul_mul_of_roots_quadratic_eq_pair` / 引理 `eq_mul_mul_of_roots_quadratic_eq_pair`

English:
lemma eq_mul_mul_of_roots_quadratic_eq_pair
  statement: [CommRing R] [IsDomain R] {a b c x1 x2 : R}
  proof: by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_

中文:
引理 eq_mul_mul_of_roots_quadratic_eq_pair
  结论: [交换环 R] [是整环 R] {a b c x1 x2 : R}
  证明: by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_

Depends on / 依赖: Multiset, Multiset.card_pair, add_comm, card_pair, card_roots, coeff_eq_esymm_roots_of_card, convert, hp_natDegree, hp_roots_card, hroots, le_antisymm, leadingCoeff, mul_assoc, natDegree, natDegree_quadratic_le, p.card_roots, p.natDegree, p.roots.card
-/
lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    c = a * x1 * x2 := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree]; rw [hroots]; rw [Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by simp [hp_natDegree])

/--
lemma `eq_neg_mul_add_of_aroots_quadratic_eq_pair` / 引理 `eq_neg_mul_add_of_aroots_quadratic_eq_pair`

English:
lemma eq_neg_mul_add_of_aroots_quadratic_eq_pair
  proof: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_neg_mul_add_of_roots_quadratic_eq_pair haroots

中文:
引理 eq_neg_mul_add_of_aroots_quadratic_eq_pair
  证明: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_neg_mul_add_of_roots_quadratic_eq_pair haroots

Depends on / 依赖: algebraMap, aroots_def, eq_neg_mul_add_of_roots_quadratic_eq_pair, haroots
-/
lemma eq_neg_mul_add_of_aroots_quadratic_eq_pair
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {a b c : T} {x1 x2 : S}
    (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S b = -algebraMap T S a * (x1 + x2) := by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_neg_mul_add_of_roots_quadratic_eq_pair haroots

/--
lemma `eq_mul_mul_of_aroots_quadratic_eq_pair` / 引理 `eq_mul_mul_of_aroots_quadratic_eq_pair`

English:
lemma eq_mul_mul_of_aroots_quadratic_eq_pair
  statement: [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
  proof: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_mul_mul_of_roots_quadratic_eq_pair haroots

中文:
引理 eq_mul_mul_of_aroots_quadratic_eq_pair
  结论: [交换环 T] [交换环 S] [是整环 S] [代数 T S]
  证明: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_mul_mul_of_roots_quadratic_eq_pair haroots

Depends on / 依赖: algebraMap, aroots_def, eq_mul_mul_of_roots_quadratic_eq_pair, haroots
-/
lemma eq_mul_mul_of_aroots_quadratic_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {a b c : T} {x1 x2 : S} (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_mul_mul_of_roots_quadratic_eq_pair haroots

/--
lemma `roots_quadratic_eq_pair_iff_of_ne_zero` / 引理 `roots_quadratic_eq_pair_iff_of_ne_zero`

English:
lemma roots_quadratic_eq_pair_iff_of_ne_zero
  statement: [CommRing R] [IsDomain R] {a b c x1 x2 : R}
  proof: have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
    suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) != 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_

中文:
引理 roots_quadratic_eq_pair_iff_of_ne_zero
  结论: [交换环 R] [是整环 R] {a b c x1 x2 : R}
  证明: have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
    suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) != 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_

Depends on / 依赖: Polynomial, Polynomial.X_sub_C_ne_zero, Polynomial.roots_mul, X_sub_C_ne_zero, eq_neg_, hvieta, mul_ne_zero, roots_mul, roots_of_ne_zero_of_vieta
-/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a != 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
  have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
    suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) != 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) != 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
    simp [hvieta.1, hvieta.2]
    ring
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair h, eq_mul_mul_of_roots_quadratic_eq_pair h⟩,
    roots_of_ne_zero_of_vieta⟩

/--
lemma `aroots_quadratic_eq_pair_iff_of_ne_zero` / 引理 `aroots_quadratic_eq_pair_iff_of_ne_zero`

English:
lemma aroots_quadratic_eq_pair_iff_of_ne_zero
  statement: [CommRing T] [CommRing S] [IsDomain S]
  proof: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero ha

中文:
引理 aroots_quadratic_eq_pair_iff_of_ne_zero
  结论: [交换环 T] [交换环 S] [是整环 S]
  证明: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero ha

Depends on / 依赖: algebraMap, aroots_def, roots_quadratic_eq_pair_iff_of_ne_zero
-/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {a b c : T} {x1 x2 : S} (ha : algebraMap T S a != 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      algebraMap T S b = -algebraMap T S a * (x1 + x2) ∧
      algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero ha

/--
lemma `roots_quadratic_eq_pair_iff_of_ne_zero'` / 引理 `roots_quadratic_eq_pair_iff_of_ne_zero'`

English:
lemma roots_quadratic_eq_pair_iff_of_ne_zero'
  given: [Field R] {a b c x1 x2 : R} (ha : a != 0)
  proof: by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha]
  grind

中文:
引理 roots_quadratic_eq_pair_iff_of_ne_zero'
  条件: [域 R] {a b c x1 x2 : R} (ha : a != 0)
  证明: by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha]
  grind

Depends on / 依赖: roots_quadratic_eq_pair_iff_of_ne_zero
-/
lemma roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {a b c x1 x2 : R} (ha : a != 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha]
  grind

/--
lemma `aroots_quadratic_eq_pair_iff_of_ne_zero'` / 引理 `aroots_quadratic_eq_pair_iff_of_ne_zero'`

English:
lemma aroots_quadratic_eq_pair_iff_of_ne_zero'
  statement: [CommRing T] [Field S] [Algebra T S] {a b c : T}
  proof: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero' ha

中文:
引理 aroots_quadratic_eq_pair_iff_of_ne_zero'
  结论: [交换环 T] [域 S] [代数 T S] {a b c : T}
  证明: by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero' ha

Depends on / 依赖: algebraMap, aroots_def, roots_quadratic_eq_pair_iff_of_ne_zero
-/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {a b c : T}
    {x1 x2 : S} (ha : algebraMap T S a != 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S b / algebraMap T S a ∧
      x1 * x2 = algebraMap T S c / algebraMap T S a := by
  rw [aroots_def]; rw [show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero' ha

end Polynomial
