/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.Data.Int.Order.Units
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Unit Trinomials

This file defines irreducible trinomials and proves an irreducibility criterion.

## Main definitions

- `Polynomial.IsUnitTrinomial`

## Main results

- `Polynomial.IsUnitTrinomial.irreducible_of_coprime`: An irreducibility criterion for unit
  trinomials.

-/

@[expose] public section

assert_not_exists TopologicalSpace

namespace Polynomial

open scoped Polynomial

open Finset

section Semiring

variable {R : Type*} [Semiring R] (k m n : Nat) (u v w : R)

/--
Definition of `trinomial` / `trinomial` 的定义

English:
definition trinomial
  body: C u * X ^ k + C v * X ^ m + C w * X ^ n

中文:
定义 trinomial
  定义体: C u * X ^ k + C v * X ^ m + C w * X ^ n
-/
noncomputable def trinomial :=
  C u * X ^ k + C v * X ^ m + C w * X ^ n

/--
theorem `trinomial_def` / 定理 `trinomial_def`

English:
theorem trinomial_def
  statement: trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n
  proof: rfl

中文:
定理 trinomial_def
  结论: trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n
  证明: rfl
-/
theorem trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n :=
  rfl

variable {k m n u v w}

/--
theorem `trinomial_leading_coeff'` / 定理 `trinomial_leading_coeff'`

English:
theorem trinomial_leading_coeff'
  given: (hkm : k < m) (hmn : m < n)
  proof: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg (hkm.trans hmn).ne']; rw [if_neg hmn.ne']; rw [if_pos rfl]; rw [zero_add]; rw [zero_add]

中文:
定理 trinomial_leading_coeff'
  条件: (hkm : k < m) (hmn : m < n)
  证明: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg (hkm.trans hmn).ne']; rw [if_neg hmn.ne']; rw [if_pos rfl]; rw [zero_add]; rw [zero_add]

Depends on / 依赖: coeff_C_mul_X_pow, coeff_add, hkm.trans, hmn.ne, if_neg, if_pos, trinomial_def, zero_add
-/
theorem trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff n = w := by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg (hkm.trans hmn).ne']; rw [if_neg hmn.ne']; rw [if_pos rfl]; rw [zero_add]; rw [zero_add]

/--
theorem `trinomial_middle_coeff` / 定理 `trinomial_middle_coeff`

English:
theorem trinomial_middle_coeff
  given: (hkm : k < m) (hmn : m < n)
  proof: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg hkm.ne']; rw [if_pos rfl]; rw [if_neg hmn.ne]; rw [zero_add]; rw [add_zero]

中文:
定理 trinomial_middle_coeff
  条件: (hkm : k < m) (hmn : m < n)
  证明: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg hkm.ne']; rw [if_pos rfl]; rw [if_neg hmn.ne]; rw [zero_add]; rw [add_zero]

Depends on / 依赖: add_zero, coeff_C_mul_X_pow, coeff_add, hkm.ne, hmn.ne, if_neg, if_pos, trinomial_def, zero_add
-/
theorem trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff m = v := by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_neg hkm.ne']; rw [if_pos rfl]; rw [if_neg hmn.ne]; rw [zero_add]; rw [add_zero]

/--
theorem `trinomial_trailing_coeff'` / 定理 `trinomial_trailing_coeff'`

English:
theorem trinomial_trailing_coeff'
  given: (hkm : k < m) (hmn : m < n)
  proof: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_pos rfl]; rw [if_neg hkm.ne]; rw [if_neg (hkm.trans hmn).ne]; rw [add_zero]; rw [add_zero]

中文:
定理 trinomial_trailing_coeff'
  条件: (hkm : k < m) (hmn : m < n)
  证明: by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_pos rfl]; rw [if_neg hkm.ne]; rw [if_neg (hkm.trans hmn).ne]; rw [add_zero]; rw [add_zero]

Depends on / 依赖: add_zero, coeff_C_mul_X_pow, coeff_add, hkm.ne, hkm.trans, if_neg, if_pos, trinomial_def
-/
theorem trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) :
    (trinomial k m n u v w).coeff k = u := by
  rw [trinomial_def]; rw [coeff_add]; rw [coeff_add]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [coeff_C_mul_X_pow]; rw [if_pos rfl]; rw [if_neg hkm.ne]; rw [if_neg (hkm.trans hmn).ne]; rw [add_zero]; rw [add_zero]

/--
theorem `trinomial_natDegree` / 定理 `trinomial_natDegree`

English:
theorem trinomial_natDegree
  given: (hkm : k < m) (hmn : m < n) (hw : w != 0)
  proof: by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
le_degree_of_ne_zero by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at h
  rcases h with (rfl | rfl

中文:
定理 trinomial_natDegree
  条件: (hkm : k < m) (hmn : m < n) (hw : w != 0)
  证明: by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
le_degree_of_ne_zero by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at h
  rcases h with (rfl | rfl

Depends on / 依赖: Finset, Finset.sup_le, WithBot, WithBot.coe_le_coe.mpr, antisymm, coe_le_coe, hkm.trans, hmn.le, le_degree_of_ne_zero, le_rfl, mem_insert, mem_singleton, natDegree_eq_of_degree_eq_some, replace, sup_le, support_trinomial_subset, trinomial_leading_coeff
-/
theorem trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w != 0) :
    (trinomial k m n u v w).natDegree = n := by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
le_degree_of_ne_zero by rwa [trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact WithBot.coe_le_coe.mpr (hkm.trans hmn).le
  · exact WithBot.coe_le_coe.mpr hmn.le
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `trinomial_natTrailingDegree` / 定理 `trinomial_natTrailingDegree`

English:
theorem trinomial_natTrailingDegree
  given: (hkm : k < m) (hmn : m < n) (hu : u != 0)
  proof: by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
trailingDegree_le_of_ne_zero by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] a

中文:
定理 trinomial_natTrailingDegree
  条件: (hkm : k < m) (hmn : m < n) (hu : u != 0)
  证明: by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
trailingDegree_le_of_ne_zero by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] a

Depends on / 依赖: Finset, Finset.le_inf, WithTop, WithTop.coe_le_coe.mpr, antisymm, coe_le_coe, hkm.le, hkm.trans, le_inf, le_rfl, mem_insert, mem_singleton, natTrailingDegree_eq_of_trailingDegree_eq_some, replace, support_trinomial_subset, trailingDegree_le_of_ne_zero, trinomial_trailing_coeff
-/
theorem trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u != 0) :
    (trinomial k m n u v w).natTrailingDegree = k := by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
trailingDegree_le_of_ne_zero by rwa [trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial_subset k m n u v w h
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact le_rfl
  · exact WithTop.coe_le_coe.mpr hkm.le
  · exact WithTop.coe_le_coe.mpr (hkm.trans hmn).le

/--
theorem `trinomial_leadingCoeff` / 定理 `trinomial_leadingCoeff`

English:
theorem trinomial_leadingCoeff
  given: (hkm : k < m) (hmn : m < n) (hw : w != 0)
  proof: by
  rw [leadingCoeff]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_leading_coeff' hkm hmn]

中文:
定理 trinomial_leadingCoeff
  条件: (hkm : k < m) (hmn : m < n) (hw : w != 0)
  证明: by
  rw [leadingCoeff]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_leading_coeff' hkm hmn]

Depends on / 依赖: leadingCoeff, trinomial_leading_coeff, trinomial_natDegree
-/
theorem trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w != 0) :
    (trinomial k m n u v w).leadingCoeff = w := by
  rw [leadingCoeff]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_leading_coeff' hkm hmn]

/--
theorem `trinomial_trailingCoeff` / 定理 `trinomial_trailingCoeff`

English:
theorem trinomial_trailingCoeff
  given: (hkm : k < m) (hmn : m < n) (hu : u != 0)
  proof: by
  rw [trailingCoeff]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [trinomial_trailing_coeff' hkm hmn]

中文:
定理 trinomial_trailingCoeff
  条件: (hkm : k < m) (hmn : m < n) (hu : u != 0)
  证明: by
  rw [trailingCoeff]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [trinomial_trailing_coeff' hkm hmn]

Depends on / 依赖: trailingCoeff, trinomial_natTrailingDegree, trinomial_trailing_coeff
-/
theorem trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u != 0) :
    (trinomial k m n u v w).trailingCoeff = u := by
  rw [trailingCoeff]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [trinomial_trailing_coeff' hkm hmn]

/--
theorem `trinomial_monic` / 定理 `trinomial_monic`

English:
theorem trinomial_monic
  given: (hkm : k < m) (hmn : m < n)
  statement: (trinomial k m n u v 1).Monic
  proof: by
  nontriviality R
  exact trinomial_leadingCoeff hkm hmn one_ne_zero

中文:
定理 trinomial_monic
  条件: (hkm : k < m) (hmn : m < n)
  结论: (trinomial k m n u v 1).Monic
  证明: by
  nontriviality R
  exact trinomial_leadingCoeff hkm hmn one_ne_zero

Depends on / 依赖: nontriviality, one_ne_zero, trinomial_leadingCoeff
-/
theorem trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).Monic := by
  nontriviality R
  exact trinomial_leadingCoeff hkm hmn one_ne_zero

/--
theorem `trinomial_mirror` / 定理 `trinomial_mirror`

English:
theorem trinomial_mirror
  given: (hkm : k < m) (hmn : m < n) (hu : u != 0) (hw : w != 0)
  proof: by
  rw [mirror]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [reverse]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_def]; rw [reflect_add]; rw [reflect_add]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [revAt_le (hkm.trans hmn).le]; rw [revAt_le hmn.l

中文:
定理 trinomial_mirror
  条件: (hkm : k < m) (hmn : m < n) (hu : u != 0) (hw : w != 0)
  证明: by
  rw [mirror]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [reverse]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_def]; rw [reflect_add]; rw [reflect_add]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [revAt_le (hkm.trans hmn).le]; rw [revAt_le hmn.l

Depends on / 依赖: Nat.sub_add_cancel, add_mul, hkm.trans, hmn.le, le_rfl, mirror, mul_assoc, pow_add, reflect_C_mul_X_pow, reflect_add, revAt_le, reverse, sub_add_cancel, trinomial_def, trinomial_natDegree, trinomial_natTrailingDegree
-/
theorem trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u != 0) (hw : w != 0) :
    (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u := by
  rw [mirror]; rw [trinomial_natTrailingDegree hkm hmn hu]; rw [reverse]; rw [trinomial_natDegree hkm hmn hw]; rw [trinomial_def]; rw [reflect_add]; rw [reflect_add]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [reflect_C_mul_X_pow]; rw [revAt_le (hkm.trans hmn).le]; rw [revAt_le hmn.le]; rw [revAt_le le_rfl]; rw [add_mul]; rw [add_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [← pow_add]; rw [← pow_add]; rw [← pow_add]; rw [Nat.sub_add_cancel (hkm.trans hmn).le]; rw [Nat.sub_self]; rw [zero_add]; rw [add_comm]; rw [add_comm (C u * X ^ n)]; rw [← add_assoc]; rw [← trinomial_def]

/--
theorem `trinomial_support` / 定理 `trinomial_support`

English:
theorem trinomial_support
  given: (hkm : k < m) (hmn : m < n) (hu : u != 0) (hv : v != 0) (hw : w != 0)
  proof: support_trinomial hkm hmn hu hv hw

中文:
定理 trinomial_support
  条件: (hkm : k < m) (hmn : m < n) (hu : u != 0) (hv : v != 0) (hw : w != 0)
  证明: support_trinomial hkm hmn hu hv hw

Depends on / 依赖: support_trinomial
-/
theorem trinomial_support (hkm : k < m) (hmn : m < n) (hu : u != 0) (hv : v != 0) (hw : w != 0) :
    (trinomial k m n u v w).support = {k, m, n} :=
  support_trinomial hkm hmn hu hv hw

end Semiring

variable (p q : Int[X])

/--
Definition of `IsUnitTrinomial` / `IsUnitTrinomial` 的定义

English:
definition IsUnitTrinomial
  body: exists (k m n : Nat) (_ : k < m) (_ : m < n) (u v w : Units Int), p = trinomial k m n (u : Int) v w

中文:
定义 IsUnitTrinomial
  定义体: exists (k m n : Nat) (_ : k < m) (_ : m < n) (u v w : Units Int), p = trinomial k m n (u : Int) v w

Depends on / 依赖: trinomial
-/
def IsUnitTrinomial :=
  exists (k m n : Nat) (_ : k < m) (_ : m < n) (u v w : Units Int), p = trinomial k m n (u : Int) v w

variable {p q}

namespace IsUnitTrinomial

/--
theorem `not_isUnit` / 定理 `not_isUnit`

English:
theorem not_isUnit
  given: (hp : p.IsUnitTrinomial)
  statement: ¬IsUnit p
  proof: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))

中文:
定理 not_isUnit
  条件: (hp : p.IsUnitTrinomial)
  结论: ¬IsUnit p
  证明: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))

Depends on / 依赖: degree_eq_zero_of_isUnit, natDegree_eq_of_degree_eq_some, ne_zero, ne_zero_of_lt, symm.trans, trinomial_natDegree, w.ne_zero
-/
theorem not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))

/--
theorem `card_support_eq_three` / 定理 `card_support_eq_three`

English:
theorem card_support_eq_three
  given: (hp : p.IsUnitTrinomial)
  statement: #p.support = 3
  proof: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero

中文:
定理 card_support_eq_three
  条件: (hp : p.IsUnitTrinomial)
  结论: #p.support = 3
  证明: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero

Depends on / 依赖: card_support_trinomial, ne_zero, u.ne_zero, v.ne_zero, w.ne_zero
-/
theorem card_support_eq_three (hp : p.IsUnitTrinomial) : #p.support = 3 := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (hp : p.IsUnitTrinomial)
  statement: p != 0
  proof: by
  rintro rfl
  simpa using hp.card_support_eq_three

中文:
定理 ne_zero
  条件: (hp : p.IsUnitTrinomial)
  结论: p != 0
  证明: by
  rintro rfl
  simpa using hp.card_support_eq_three

Depends on / 依赖: card_support_eq_three, hp.card_support_eq_three
-/
theorem ne_zero (hp : p.IsUnitTrinomial) : p != 0 := by
  rintro rfl
  simpa using hp.card_support_eq_three

/--
theorem `coeff_isUnit` / 定理 `coeff_isUnit`

English:
theorem coeff_isUnit
  given: (hp : p.IsUnitTrinomial) {k : Nat} (hk : k in p.support)
  proof: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial_subset k m n (u : Int) v w hk
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [trinomial_

中文:
定理 coeff_isUnit
  条件: (hp : p.IsUnitTrinomial) {k : 自然数} (hk : k in p.support)
  证明: by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial_subset k m n (u : Int) v w hk
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [trinomial_

Depends on / 依赖: mem_insert, mem_singleton, support_trinomial_subset, trinomial_leading_coeff, trinomial_middle_coeff, trinomial_trailing_coeff
-/
theorem coeff_isUnit (hp : p.IsUnitTrinomial) {k : Nat} (hk : k in p.support) :
    IsUnit (p.coeff k) := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial_subset k m n (u : Int) v w hk
  rw [mem_insert]; rw [mem_insert]; rw [mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [trinomial_middle_coeff hkm hmn]⟩
  · refine ⟨w, by rw [trinomial_leading_coeff' hkm hmn]⟩

/--
theorem `leadingCoeff_isUnit` / 定理 `leadingCoeff_isUnit`

English:
theorem leadingCoeff_isUnit
  given: (hp : p.IsUnitTrinomial)
  statement: IsUnit p.leadingCoeff
  proof: hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)

中文:
定理 leadingCoeff_isUnit
  条件: (hp : p.IsUnitTrinomial)
  结论: IsUnit p.leadingCoeff
  证明: hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)

Depends on / 依赖: coeff_isUnit, hp.coeff_isUnit, hp.ne_zero, natDegree_mem_support_of_nonzero, ne_zero
-/
theorem leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff :=
  hp.coeff_isUnit (natDegree_mem_support_of_nonzero hp.ne_zero)

/--
theorem `trailingCoeff_isUnit` / 定理 `trailingCoeff_isUnit`

English:
theorem trailingCoeff_isUnit
  given: (hp : p.IsUnitTrinomial)
  statement: IsUnit p.trailingCoeff
  proof: hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)

中文:
定理 trailingCoeff_isUnit
  条件: (hp : p.IsUnitTrinomial)
  结论: IsUnit p.trailingCoeff
  证明: hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)

Depends on / 依赖: coeff_isUnit, hp.coeff_isUnit, hp.ne_zero, natTrailingDegree_mem_support_of_nonzero, ne_zero
-/
theorem trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff :=
  hp.coeff_isUnit (natTrailingDegree_mem_support_of_nonzero hp.ne_zero)

end IsUnitTrinomial

/--
theorem `isUnitTrinomial_iff` / 定理 `isUnitTrinomial_iff`

English:
theorem isUnitTrinomial_iff
  proof: by
  refine ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m 

中文:
定理 isUnitTrinomial_iff
  证明: by
  refine ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m 

Depends on / 依赖: card_support_eq_three, card_support_eq_three.mp, coeff_C_mul, coeff_X_pow, coeff_X_pow_self, coeff_add, coeff_isUnit, hp.card_support_eq_three, hp.coeff_isUnit, mem_insert_of_mem, mem_insert_self, mem_singleton_self, mul_one, replace, simp_rw, support_trinomial
-/
theorem isUnitTrinomial_iff :
    p.IsUnitTrinomial ↔ #p.support = 3 ∧ forall k in p.support, IsUnit (p.coeff k) := by
  refine ⟨fun hp => ⟨hp.card_support_eq_three, fun k => hp.coeff_isUnit⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n}))
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n)))
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz
  rw [if_neg hkm.ne]; rw [if_neg (hkm.trans hmn).ne] at hx
  rw [if_neg hkm.ne']; rw [if_neg hmn.ne] at hy
  rw [if_neg (hkm.trans hmn).ne']; rw [if_neg hmn.ne'] at hz
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz
  exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩

/--
theorem `isUnitTrinomial_iff'` / 定理 `isUnitTrinomial_iff'`

English:
theorem isUnitTrinomial_iff'
  proof: by
  rw [natDegree_mul_mirror]; rw [natTrailingDegree_mul_mirror]; rw [← mul_add]; rw [Nat.mul_div_right _ zero_lt_two]; rw [coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def]; rw [trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero]; rw [

中文:
定理 isUnitTrinomial_iff'
  证明: by
  rw [natDegree_mul_mirror]; rw [natTrailingDegree_mul_mirror]; rw [← mul_add]; rw [Nat.mul_div_right _ zero_lt_two]; rw [coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def]; rw [trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero]; rw [

Depends on / 依赖: Nat.mul_div_right, coeff_mul_mirror, hkm.ne, hkm.trans, hmn.ne, mem_insert, mem_insert.mp, mem_singleton, mem_singleton.mp, mul_add, mul_div_right, natDegree_mul_mirror, natTrailingDegree_mul_mirror, ne_zero, not_or_intro, sum_def, sum_insert, sum_singleton, trinom, trinomial_leading_coeff
-/
theorem isUnitTrinomial_iff' :
    p.IsUnitTrinomial ↔
      (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailingDegree) / 2) =
        3 := by
  rw [natDegree_mul_mirror]; rw [natTrailingDegree_mul_mirror]; rw [← mul_add]; rw [Nat.mul_div_right _ zero_lt_two]; rw [coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def]; rw [trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero]; rw [sum_insert (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne)))]; rw [sum_insert (mt mem_singleton.mp hmn.ne)]; rw [sum_singleton]; rw [trinomial_leading_coeff' hkm hmn]; rw [trinomial_middle_coeff hkm hmn]; rw [trinomial_trailing_coeff' hkm hmn]
    simp_rw [← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one]
    decide
  · have key : forall k in p.support, p.coeff k ^ 2 = 1 := fun k hk =>
      Int.sq_eq_one_of_sq_le_three
        ((single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk)
    refine isUnitTrinomial_iff.mpr ⟨?_, fun k hk => .of_pow_eq_one (key k hk) two_ne_zero⟩
    rw [sum_def]; rw [sum_congr rfl key]; rw [sum_const]; rw [Nat.smul_one_eq_cast] at hp
    exact Nat.cast_injective hp

/--
theorem `isUnitTrinomial_iff''` / 定理 `isUnitTrinomial_iff''`

English:
theorem isUnitTrinomial_iff''
  given: (h : p * p.mirror = q * q.mirror)
  proof: by
  rw [isUnitTrinomial_iff']; rw [isUnitTrinomial_iff']; rw [h]

中文:
定理 isUnitTrinomial_iff''
  条件: (h : p * p.mirror = q * q.mirror)
  证明: by
  rw [isUnitTrinomial_iff']; rw [isUnitTrinomial_iff']; rw [h]

Depends on / 依赖: isUnitTrinomial_iff
-/
theorem isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) :
    p.IsUnitTrinomial ↔ q.IsUnitTrinomial := by
  rw [isUnitTrinomial_iff']; rw [isUnitTrinomial_iff']; rw [h]

namespace IsUnitTrinomial

/--
theorem `irreducible_aux1` / 定理 `irreducible_aux1`

English:
theorem irreducible_aux1
  statement: {k m n : Nat} (hkm : k < m) (hmn : m < n) (u v w : Units Int)
  proof: by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp]; rw [trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidA

中文:
定理 irreducible_aux1
  结论: {k m n : 自然数} (hkm : k < m) (hmn : m < n) (u v w : Units 整数)
  证明: by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp]; rw [trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidA

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single, C_mul_X_pow_eq_monomial, Finsupp, Finsupp.filter_add, Finsupp.filter_single_of_neg, add_mul, coeff_add, coeff_single, filter_add, filter_single_of_neg, hmn.le, lt_tsub_iff_right, monomial_mul_monomial, mul_add, ne_zero, simp_rw, toFinsupp_add, toFinsupp_monomial
-/
theorem irreducible_aux1 {k m n : Nat} (hkm : k < m) (hmn : m < n) (u v w : Units Int)
    (hp : p = trinomial k m n (u : Int) v w) :
    C (v : Int) * (C (u : Int) * X ^ (m + n) + C (w : Int) * X ^ (n - m + k + n)) =
⟨.ofCoeff (p * p.mirror).toFinsupp.coeff.filter (· in Set.Ioo (k + n) (n + n))⟩ := by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp]; rw [trinomial_mirror hkm hmn u.ne_zero w.ne_zero]
  simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidAlgebra.coeff_add, Finsupp.filter_add,
    AddMonoidAlgebra.coeff_single]
  rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_pos]; rw [Finsupp.filter_single_of_neg]; rw [Finsupp.filter_single_of_pos]; rw [Finsupp.filter_single_of_neg]
  · simp only [add_zero, zero_add, AddMonoidAlgebra.ofCoeff_add, ofFinsupp_add,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single, C_mul_monomial, C_mul_monomial,
      mul_comm (v : Int) w, add_comm (n - m + k) n]
  · simp
  · refine ⟨?_, by gcongr⟩
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt]
  · exact fun h => h.1.ne (add_comm k n)
  · constructor <;> gcongr
  · rw [← add_assoc, add_tsub_cancel_of_le hmn.le, add_comm]
    exact fun h => h.1.ne rfl
  · grind
  · exact fun h => h.1.ne rfl
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) key
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn)

/--
theorem `irreducible_aux2` / 定理 `irreducible_aux2`

English:
theorem irreducible_aux2
  statement: {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  proof: by
let f (p : Int[X]) : Int[X] := ⟨.ofCoeff .filter (· in Set.Ioo (k + n) (n + n)) p.toFinsupp.coeff⟩
  replace h := congr_arg f h
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj]

中文:
定理 irreducible_aux2
  结论: {k m m' n : 自然数} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  证明: by
let f (p : Int[X]) : Int[X] := ⟨.ofCoeff .filter (· in Set.Ioo (k + n) (n + n)) p.toFinsupp.coeff⟩
  replace h := congr_arg f h
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj]

Depends on / 依赖: Or.inl, Or.inr, Set.Ioo, Units.val_inj, add_left_inj, binomial_eq_binomial, congr_arg, filter, h.trans, hp.symm, hq.trans, irreducible_aux1, isUnit, isUnit_C, isUnit_C.mpr, mul_right_inj, ne_zero, ofCoeff, p.toFinsupp.coeff, replace
-/
theorem irreducible_aux2 {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w : Units Int) (hp : p = trinomial k m n (u : Int) v w) (hq : q = trinomial k m' n (u : Int) v w)
    (h : p * p.mirror = q * q.mirror) : q = p ∨ q = p.mirror := by
let f (p : Int[X]) : Int[X] := ⟨.ofCoeff .filter (· in Set.Ioo (k + n) (n + n)) p.toFinsupp.coeff⟩
  replace h := congr_arg f h
  replace h := (irreducible_aux1 hkm hmn u v w hp).trans h
  replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm
  rw [(isUnit_C.mpr v.isUnit).mul_right_inj] at h
  rw [binomial_eq_binomial u.ne_zero w.ne_zero] at h
  simp only [add_left_inj, Units.val_inj] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩)
  · exact Or.inl (hq.trans hp.symm)
  · refine Or.inr ?_
    rw [← trinomial_mirror hkm' hmn' u.ne_zero u.ne_zero]; rw [eq_comm]; rw [mirror_eq_iff] at hp
    exact hq.trans hp
  · grind

/--
theorem `irreducible_aux3` / 定理 `irreducible_aux3`

English:
theorem irreducible_aux3
  statement: {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  proof: by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul]; rw [leadingCoeff_mul]; rw [mirror_leadingCoeff]; rw [mirror_leadingCoeff]; rw [hp]; rw [hq]; rw [trinomial_leadingCoeff hkm hmn w.ne_zero]; rw [trinomial_leadingCoeff hkm' hmn' z.ne_zero]; rw [trinomial_trailingCoeff hkm hmn u.ne_ze

中文:
定理 irreducible_aux3
  结论: {k m m' n : 自然数} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  证明: by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul]; rw [leadingCoeff_mul]; rw [mirror_leadingCoeff]; rw [mirror_leadingCoeff]; rw [hp]; rw [hq]; rw [trinomial_leadingCoeff hkm hmn w.ne_zero]; rw [trinomial_leadingCoeff hkm' hmn' z.ne_zero]; rw [trinomial_trailingCoeff hkm hmn u.ne_ze

Depends on / 依赖: congr_arg, eval_mul, leadingCoeff, leadingCoeff_mul, mirror_eval_one, mirror_leadingCoeff, ne_zero, trinomial_leadingCoeff, trinomial_trailingCoeff, u.ne_zero, w.ne_zero, x.ne_zero, z.ne_zero
-/
theorem irreducible_aux3 {k m m' n : Nat} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w x z : Units Int) (hp : p = trinomial k m n (u : Int) v w)
    (hq : q = trinomial k m' n (x : Int) v z) (h : p * p.mirror = q * q.mirror) :
    q = p ∨ q = p.mirror := by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul]; rw [leadingCoeff_mul]; rw [mirror_leadingCoeff]; rw [mirror_leadingCoeff]; rw [hp]; rw [hq]; rw [trinomial_leadingCoeff hkm hmn w.ne_zero]; rw [trinomial_leadingCoeff hkm' hmn' z.ne_zero]; rw [trinomial_trailingCoeff hkm hmn u.ne_zero]; rw [trinomial_trailingCoeff hkm' hmn' x.ne_zero]
    at hmul
  have hadd := congr_arg (eval 1) h
  rw [eval_mul]; rw [eval_mul]; rw [mirror_eval_one]; rw [mirror_eval_one]; rw [← sq]; rw [← sq]; rw [hp]; rw [hq] at hadd
  simp only [eval_add, eval_C_mul, eval_X_pow, one_pow, mul_one, trinomial_def] at hadd
  rw [add_assoc]; rw [add_assoc]; rw [add_comm (u : Int)]; rw [add_comm (x : Int)]; rw [add_assoc]; rw [add_assoc] at hadd
  simp only [add_sq', add_assoc, add_right_inj, ← Units.val_pow_eq_pow_val, Int.units_sq] at hadd
  rw [mul_assoc]; rw [hmul]; rw [← mul_assoc]; rw [add_right_inj]; rw [mul_right_inj' (show 2 * (v : Int) != 0 from mul_ne_zero two_ne_zero v.ne_zero)] at hadd
  replace hadd :=
    (Int.isUnit_add_isUnit_eq_isUnit_add_isUnit w.isUnit u.isUnit z.isUnit x.isUnit).mp hadd
  simp only [Units.val_inj] at hadd
  rcases hadd with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h
  · rw [← mirror_inj, trinomial_mirror hkm' hmn' w.ne_zero u.ne_zero] at hq
    rw [mul_comm q]; rw [← q.mirror_mirror]; rw [q.mirror.mirror_mirror] at h
    rw [← mirror_inj]; rw [or_comm]; rw [← mirror_eq_iff]
    exact
      irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
        (lt_tsub_iff_right.mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h

/--
theorem `irreducible_of_coprime` / 定理 `irreducible_of_coprime`

English:
theorem irreducible_of_coprime
  statement: (hp : p.IsUnitTrinomial)
  proof: by
  refine irreducible_of_mirror hp.not_isUnit (fun q hpq => ?_) h
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 != 0 f

中文:
定理 irreducible_of_coprime
  结论: (hp : p.IsUnitTrinomial)
  证明: by
  refine irreducible_of_mirror hp.not_isUnit (fun q hpq => ?_) h
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 != 0 f

Depends on / 依赖: IsUnitTrinomial, hp.not_isUnit, irreducible_of_mirror, isUnitTrinomial_iff, mul_right_inj, natTrailingDegree_mul_mirror, ne_zero, not_isUnit, trinomial_natTrailingDegree, two_ne_zero, u.ne_zero
-/
theorem irreducible_of_coprime (hp : p.IsUnitTrinomial)
    (h : IsRelPrime p p.mirror) : Irreducible p := by
  refine irreducible_of_mirror hp.not_isUnit (fun q hpq => ?_) h
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 != 0 from two_ne_zero)]; rw [←
      trinomial_natTrailingDegree hkm hmn u.ne_zero]; rw [← hp]; rw [← natTrailingDegree_mul_mirror]; rw [hpq]; rw [natTrailingDegree_mul_mirror]; rw [hq]; rw [trinomial_natTrailingDegree hkm' hmn' x.ne_zero]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 != 0 from two_ne_zero)]; rw [← trinomial_natDegree hkm hmn w.ne_zero]; rw [←
      hp]; rw [← natDegree_mul_mirror]; rw [hpq]; rw [natDegree_mul_mirror]; rw [hq]; rw [trinomial_natDegree hkm' hmn' z.ne_zero]
  subst hk
  subst hn
  rcases eq_or_eq_neg_of_sq_eq_sq (y : Int) (v : Int)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · rw [h1] at hq
    rcases irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rw [h1] at hq
    rw [trinomial_def] at hp
    rw [← neg_inj]; rw [neg_add]; rw [neg_add]; rw [← neg_mul]; rw [← neg_mul]; rw [← neg_mul]; rw [← C_neg]; rw [← C_neg]; rw [← C_neg]
      at hp
    rw [← neg_mul_neg]; rw [← mirror_neg] at hpq
    rcases irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))

/--
theorem `irreducible_of_isCoprime` / 定理 `irreducible_of_isCoprime`

English:
theorem irreducible_of_isCoprime
  given: (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror)
  proof: irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

中文:
定理 irreducible_of_isCoprime
  条件: (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror)
  证明: irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

Depends on / 依赖: h.isUnit_of_dvd, irreducible_of_coprime, isUnit_of_dvd
-/
theorem irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror) :
    Irreducible p :=
  irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

end IsUnitTrinomial

end Polynomial
