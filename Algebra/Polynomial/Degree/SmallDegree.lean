/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Nat.WithBot

/-!
# Results on polynomials of specific small degrees
-/

public section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

/--
theorem `eq_X_add_C_of_degree_le_one` / 定理 `eq_X_add_C_of_degree_le_one`

English:
theorem eq_X_add_C_of_degree_le_one
  given: (h : degree p <= 1)
  statement: p = C (p.coeff 1) * X + C (p.coeff 0)
  proof: ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp) fun m => by
        have : degree p < m.succ.succ := lt_of_le_of_lt h Nat.one_lt_ofNat
        simp [coeff_eq_zero_of_degree_lt this]

中文:
定理 eq_X_add_C_of_degree_le_one
  条件: (h : degree p <= 1)
  结论: p = C (p.coeff 1) * X + C (p.coeff 0)
  证明: ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp) fun m => by
        have : degree p < m.succ.succ := lt_of_le_of_lt h Nat.one_lt_ofNat
        simp [coeff_eq_zero_of_degree_lt this]

Depends on / 依赖: Nat.casesOn, Nat.one_lt_ofNat, casesOn, coeff_eq_zero_of_degree_lt, degree, lt_of_le_of_lt, m.succ.succ, one_lt_ofNat
-/
theorem eq_X_add_C_of_degree_le_one (h : degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp) fun m => by
        have : degree p < m.succ.succ := lt_of_le_of_lt h Nat.one_lt_ofNat
        simp [coeff_eq_zero_of_degree_lt this]

/--
theorem `eq_X_add_C_of_degree_eq_one` / 定理 `eq_X_add_C_of_degree_eq_one`

English:
theorem eq_X_add_C_of_degree_eq_one
  given: (h : degree p = 1)
  proof: (eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])

中文:
定理 eq_X_add_C_of_degree_eq_one
  条件: (h : degree p = 1)
  证明: (eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])

Depends on / 依赖: Nat.cast_one, cast_one, eq_X_add_C_of_degree_le_one, h.le, leadingCoeff, natDegree_eq_of_degree_eq_some
-/
theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = C p.leadingCoeff * X + C (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])

/--
theorem `eq_X_add_C_of_natDegree_le_one` / 定理 `eq_X_add_C_of_natDegree_le_one`

English:
theorem eq_X_add_C_of_natDegree_le_one
  given: (h : natDegree p <= 1)
  proof: eq_X_add_C_of_degree_le_one degree_le_of_natDegree_le h

中文:
定理 eq_X_add_C_of_natDegree_le_one
  条件: (h : natDegree p <= 1)
  证明: eq_X_add_C_of_degree_le_one degree_le_of_natDegree_le h

Depends on / 依赖: degree_le_of_natDegree_le, eq_X_add_C_of_degree_le_one
-/
theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p <= 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) :=
eq_X_add_C_of_degree_le_one degree_le_of_natDegree_le h

/--
theorem `Monic.eq_X_add_C` / 定理 `Monic.eq_X_add_C`

English:
theorem Monic.eq_X_add_C
  given: (hm : p.Monic) (hnd : p.natDegree = 1)
  statement: p = X + C (p.coeff 0)
  proof: by
  rw [← one_mul X]; rw [← C_1]; rw [← hm.coeff_natDegree]; rw [hnd]; rw [← eq_X_add_C_of_natDegree_le_one hnd.le]

中文:
定理 Monic.eq_X_add_C
  条件: (hm : p.Monic) (hnd : p.natDegree = 1)
  结论: p = X + C (p.coeff 0)
  证明: by
  rw [← one_mul X]; rw [← C_1]; rw [← hm.coeff_natDegree]; rw [hnd]; rw [← eq_X_add_C_of_natDegree_le_one hnd.le]

Depends on / 依赖: coeff_natDegree, eq_X_add_C_of_natDegree_le_one, hm.coeff_natDegree, hnd.le, one_mul
-/
theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = X + C (p.coeff 0) := by
  rw [← one_mul X]; rw [← C_1]; rw [← hm.coeff_natDegree]; rw [hnd]; rw [← eq_X_add_C_of_natDegree_le_one hnd.le]

/--
theorem `exists_eq_X_add_C_of_natDegree_le_one` / 定理 `exists_eq_X_add_C_of_natDegree_le_one`

English:
theorem exists_eq_X_add_C_of_natDegree_le_one
  given: (h : natDegree p <= 1)
  statement: exists a b, p = C a * X + C b
  proof: ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩

中文:
定理 exists_eq_X_add_C_of_natDegree_le_one
  条件: (h : natDegree p <= 1)
  结论: 存在 a b, p = C a * X + C b
  证明: ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩

Depends on / 依赖: eq_X_add_C_of_natDegree_le_one, p.coeff
-/
theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p <= 1) : exists a b, p = C a * X + C b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/--
theorem `zero_le_degree_iff` / 定理 `zero_le_degree_iff`

English:
theorem zero_le_degree_iff
  statement: 0 <= degree p ↔ p != 0
  proof: by
  rw [← not_lt]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]

中文:
定理 zero_le_degree_iff
  结论: 0 <= degree p ↔ p != 0
  证明: by
  rw [← not_lt]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]

Depends on / 依赖: Nat.WithBot.lt_zero_iff, WithBot, degree_eq_bot, lt_zero_iff, not_lt
-/
theorem zero_le_degree_iff : 0 <= degree p ↔ p != 0 := by
  rw [← not_lt]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]

/--
theorem `ne_zero_of_coe_le_degree` / 定理 `ne_zero_of_coe_le_degree`

English:
theorem ne_zero_of_coe_le_degree
  given: (hdeg : ↑n <= p.degree)
  statement: p != 0
  proof: zero_le_degree_iff.mp (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg

中文:
定理 ne_zero_of_coe_le_degree
  条件: (hdeg : ↑n <= p.degree)
  结论: p != 0
  证明: zero_le_degree_iff.mp (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg

Depends on / 依赖: WithBot, WithBot.coe_le_coe.mpr, coe_le_coe, n.zero_le, zero_le, zero_le_degree_iff, zero_le_degree_iff.mp
-/
theorem ne_zero_of_coe_le_degree (hdeg : ↑n <= p.degree) : p != 0 :=
zero_le_degree_iff.mp (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg

/--
theorem `le_natDegree_of_coe_le_degree` / 定理 `le_natDegree_of_coe_le_degree`

English:
theorem le_natDegree_of_coe_le_degree
  given: (hdeg : ↑n <= p.degree)
  statement: n <= p.natDegree
  proof: WithBot.coe_le_coe.mp by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg

中文:
定理 le_natDegree_of_coe_le_degree
  条件: (hdeg : ↑n <= p.degree)
  结论: n <= p.natDegree
  证明: WithBot.coe_le_coe.mp by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg

Depends on / 依赖: WithBot, WithBot.coe_le_coe.mp, coe_le_coe, degree_eq_natDegree, ne_zero_of_coe_le_degree
-/
theorem le_natDegree_of_coe_le_degree (hdeg : ↑n <= p.degree) : n <= p.natDegree :=
WithBot.coe_le_coe.mp by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg

/--
theorem `degree_linear_le` / 定理 `degree_linear_le`

English:
theorem degree_linear_le
  statement: degree (C a * X + C b) <= 1
  proof: degree_add_le_of_degree_le (degree_C_mul_X_le _) le_trans degree_C_le Nat.WithBot.coe_nonneg

中文:
定理 degree_linear_le
  结论: degree (C a * X + C b) <= 1
  证明: degree_add_le_of_degree_le (degree_C_mul_X_le _) le_trans degree_C_le Nat.WithBot.coe_nonneg

Depends on / 依赖: Nat.WithBot.coe_nonneg, WithBot, coe_nonneg, degree_C_le, degree_C_mul_X_le, degree_add_le_of_degree_le, le_trans
-/
theorem degree_linear_le : degree (C a * X + C b) <= 1 :=
degree_add_le_of_degree_le (degree_C_mul_X_le _) le_trans degree_C_le Nat.WithBot.coe_nonneg

/--
theorem `degree_linear_lt` / 定理 `degree_linear_lt`

English:
theorem degree_linear_lt
  statement: degree (C a * X + C b) < 2
  proof: degree_linear_le.trans_lt WithBot.coe_lt_coe.mpr one_lt_two

@[simp]

中文:
定理 degree_linear_lt
  结论: degree (C a * X + C b) < 2
  证明: degree_linear_le.trans_lt WithBot.coe_lt_coe.mpr one_lt_two

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, degree_linear_le, degree_linear_le.trans_lt, one_lt_two, trans_lt
-/
theorem degree_linear_lt : degree (C a * X + C b) < 2 :=
degree_linear_le.trans_lt WithBot.coe_lt_coe.mpr one_lt_two

@[simp]
/--
theorem `degree_linear` / 定理 `degree_linear`

English:
theorem degree_linear
  given: (ha : a != 0)
  statement: degree (C a * X + C b) = 1
  proof: by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha]; rw [degree_C_mul_X ha]

中文:
定理 degree_linear
  条件: (ha : a != 0)
  结论: degree (C a * X + C b) = 1
  证明: by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha]; rw [degree_C_mul_X ha]

Depends on / 依赖: degree_C_lt_degree_C_mul_X, degree_C_mul_X, degree_add_eq_left_of_degree_lt
-/
theorem degree_linear (ha : a != 0) : degree (C a * X + C b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha]; rw [degree_C_mul_X ha]

/--
theorem `natDegree_linear_le` / 定理 `natDegree_linear_le`

English:
theorem natDegree_linear_le
  statement: natDegree (C a * X + C b) <= 1
  proof: natDegree_le_of_degree_le degree_linear_le

中文:
定理 natDegree_linear_le
  结论: natDegree (C a * X + C b) <= 1
  证明: natDegree_le_of_degree_le degree_linear_le

Depends on / 依赖: degree_linear_le, natDegree_le_of_degree_le
-/
theorem natDegree_linear_le : natDegree (C a * X + C b) <= 1 :=
  natDegree_le_of_degree_le degree_linear_le

/--
theorem `natDegree_linear` / 定理 `natDegree_linear`

English:
theorem natDegree_linear
  given: (ha : a != 0)
  statement: natDegree (C a * X + C b) = 1
  proof: by
  rw [natDegree_add_C]; rw [natDegree_C_mul_X a ha]

@[simp]

中文:
定理 natDegree_linear
  条件: (ha : a != 0)
  结论: natDegree (C a * X + C b) = 1
  证明: by
  rw [natDegree_add_C]; rw [natDegree_C_mul_X a ha]

@[simp]

Depends on / 依赖: natDegree_C_mul_X, natDegree_add_C
-/
theorem natDegree_linear (ha : a != 0) : natDegree (C a * X + C b) = 1 := by
  rw [natDegree_add_C]; rw [natDegree_C_mul_X a ha]

@[simp]
/--
theorem `leadingCoeff_linear` / 定理 `leadingCoeff_linear`

English:
theorem leadingCoeff_linear
  given: (ha : a != 0)
  statement: leadingCoeff (C a * X + C b) = a
  proof: by
  rw [add_comm]; rw [leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha)]; rw [leadingCoeff_C_mul_X]

中文:
定理 leadingCoeff_linear
  条件: (ha : a != 0)
  结论: leadingCoeff (C a * X + C b) = a
  证明: by
  rw [add_comm]; rw [leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha)]; rw [leadingCoeff_C_mul_X]

Depends on / 依赖: add_comm, degree_C_lt_degree_C_mul_X, leadingCoeff_C_mul_X, leadingCoeff_add_of_degree_lt
-/
theorem leadingCoeff_linear (ha : a != 0) : leadingCoeff (C a * X + C b) = a := by
  rw [add_comm]; rw [leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha)]; rw [leadingCoeff_C_mul_X]

/--
theorem `degree_quadratic_le` / 定理 `degree_quadratic_le`

English:
theorem degree_quadratic_le
  statement: degree (C a * X ^ 2 + C b * X + C c) <= 2
  proof: by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)

中文:
定理 degree_quadratic_le
  结论: degree (C a * X ^ 2 + C b * X + C c) <= 2
  证明: by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)

Depends on / 依赖: WithBot, WithBot.coe_le_coe.mpr, add_assoc, coe_le_coe, degree_C_mul_X_pow_le, degree_add_le_of_degree_le, degree_linear_le, le_trans, one_le_two
-/
theorem degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) <= 2 := by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)

/--
theorem `degree_quadratic_lt` / 定理 `degree_quadratic_lt`

English:
theorem degree_quadratic_lt
  statement: degree (C a * X ^ 2 + C b * X + C c) < 3
  proof: degree_quadratic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 2

中文:
定理 degree_quadratic_lt
  结论: degree (C a * X ^ 2 + C b * X + C c) < 3
  证明: degree_quadratic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 2

Depends on / 依赖: WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, degree_quadratic_le, degree_quadratic_le.trans_lt, lt_add_one, trans_lt
-/
theorem degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3 :=
degree_quadratic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 2

/--
theorem `degree_linear_lt_degree_C_mul_X_sq` / 定理 `degree_linear_lt_degree_C_mul_X_sq`

English:
theorem degree_linear_lt_degree_C_mul_X_sq
  given: (ha : a != 0)
  proof: by
  simpa only [degree_C_mul_X_pow 2 ha] using! degree_linear_lt

@[simp]

中文:
定理 degree_linear_lt_degree_C_mul_X_sq
  条件: (ha : a != 0)
  证明: by
  simpa only [degree_C_mul_X_pow 2 ha] using! degree_linear_lt

@[simp]

Depends on / 依赖: degree_C_mul_X_pow, degree_linear_lt
-/
theorem degree_linear_lt_degree_C_mul_X_sq (ha : a != 0) :
    degree (C b * X + C c) < degree (C a * X ^ 2) := by
  simpa only [degree_C_mul_X_pow 2 ha] using! degree_linear_lt

@[simp]
/--
theorem `degree_quadratic` / 定理 `degree_quadratic`

English:
theorem degree_quadratic
  given: (ha : a != 0)
  statement: degree (C a * X ^ 2 + C b * X + C c) = 2
  proof: by
  rw [add_assoc]; rw [degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [degree_C_mul_X_pow 2 ha]
  rfl

中文:
定理 degree_quadratic
  条件: (ha : a != 0)
  结论: degree (C a * X ^ 2 + C b * X + C c) = 2
  证明: by
  rw [add_assoc]; rw [degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [degree_C_mul_X_pow 2 ha]
  rfl

Depends on / 依赖: add_assoc, degree_C_mul_X_pow, degree_add_eq_left_of_degree_lt, degree_linear_lt_degree_C_mul_X_sq
-/
theorem degree_quadratic (ha : a != 0) : degree (C a * X ^ 2 + C b * X + C c) = 2 := by
  rw [add_assoc]; rw [degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [degree_C_mul_X_pow 2 ha]
  rfl

/--
theorem `natDegree_quadratic_le` / 定理 `natDegree_quadratic_le`

English:
theorem natDegree_quadratic_le
  statement: natDegree (C a * X ^ 2 + C b * X + C c) <= 2
  proof: natDegree_le_of_degree_le degree_quadratic_le

中文:
定理 natDegree_quadratic_le
  结论: natDegree (C a * X ^ 2 + C b * X + C c) <= 2
  证明: natDegree_le_of_degree_le degree_quadratic_le

Depends on / 依赖: degree_quadratic_le, natDegree_le_of_degree_le
-/
theorem natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) <= 2 :=
  natDegree_le_of_degree_le degree_quadratic_le

/--
theorem `natDegree_quadratic` / 定理 `natDegree_quadratic`

English:
theorem natDegree_quadratic
  given: (ha : a != 0)
  statement: natDegree (C a * X ^ 2 + C b * X + C c) = 2
  proof: natDegree_eq_of_degree_eq_some degree_quadratic ha

@[simp]

中文:
定理 natDegree_quadratic
  条件: (ha : a != 0)
  结论: natDegree (C a * X ^ 2 + C b * X + C c) = 2
  证明: natDegree_eq_of_degree_eq_some degree_quadratic ha

@[simp]

Depends on / 依赖: degree_quadratic, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_quadratic (ha : a != 0) : natDegree (C a * X ^ 2 + C b * X + C c) = 2 :=
natDegree_eq_of_degree_eq_some degree_quadratic ha

@[simp]
/--
theorem `leadingCoeff_quadratic` / 定理 `leadingCoeff_quadratic`

English:
theorem leadingCoeff_quadratic
  given: (ha : a != 0)
  statement: leadingCoeff (C a * X ^ 2 + C b * X + C c) = a
  proof: by
  rw [add_assoc]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [leadingCoeff_C_mul_X_pow]

中文:
定理 leadingCoeff_quadratic
  条件: (ha : a != 0)
  结论: leadingCoeff (C a * X ^ 2 + C b * X + C c) = a
  证明: by
  rw [add_assoc]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [leadingCoeff_C_mul_X_pow]

Depends on / 依赖: add_assoc, add_comm, degree_linear_lt_degree_C_mul_X_sq, leadingCoeff_C_mul_X_pow, leadingCoeff_add_of_degree_lt
-/
theorem leadingCoeff_quadratic (ha : a != 0) : leadingCoeff (C a * X ^ 2 + C b * X + C c) = a := by
  rw [add_assoc]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha]; rw [leadingCoeff_C_mul_X_pow]

/--
theorem `degree_cubic_le` / 定理 `degree_cubic_le`

English:
theorem degree_cubic_le
  statement: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3
  proof: by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

中文:
定理 degree_cubic_le
  结论: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3
  证明: by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

Depends on / 依赖: Nat.le_succ, WithBot, WithBot.coe_le_coe.mpr, add_assoc, coe_le_coe, degree_C_mul_X_pow_le, degree_add_le_of_degree_le, degree_quadratic_le, le_succ, le_trans
-/
theorem degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3 := by
  simpa only [add_assoc] using!
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

/--
theorem `degree_cubic_lt` / 定理 `degree_cubic_lt`

English:
theorem degree_cubic_lt
  statement: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4
  proof: degree_cubic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 3

中文:
定理 degree_cubic_lt
  结论: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4
  证明: degree_cubic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 3

Depends on / 依赖: WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, degree_cubic_le, degree_cubic_le.trans_lt, lt_add_one, trans_lt
-/
theorem degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4 :=
degree_cubic_le.trans_lt WithBot.coe_lt_coe.mpr lt_add_one 3

/--
theorem `degree_quadratic_lt_degree_C_mul_X_cb` / 定理 `degree_quadratic_lt_degree_C_mul_X_cb`

English:
theorem degree_quadratic_lt_degree_C_mul_X_cb
  given: (ha : a != 0)
  proof: by
  simpa only [degree_C_mul_X_pow 3 ha] using! degree_quadratic_lt

@[simp]

中文:
定理 degree_quadratic_lt_degree_C_mul_X_cb
  条件: (ha : a != 0)
  证明: by
  simpa only [degree_C_mul_X_pow 3 ha] using! degree_quadratic_lt

@[simp]

Depends on / 依赖: degree_C_mul_X_pow, degree_quadratic_lt
-/
theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a != 0) :
    degree (C b * X ^ 2 + C c * X + C d) < degree (C a * X ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using! degree_quadratic_lt

@[simp]
/--
theorem `degree_cubic` / 定理 `degree_cubic`

English:
theorem degree_cubic
  given: (ha : a != 0)
  statement: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3
  proof: by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [degree_add_eq_left_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [degree_C_mul_X_pow 3 ha]
  rfl

中文:
定理 degree_cubic
  条件: (ha : a != 0)
  结论: degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3
  证明: by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [degree_add_eq_left_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [degree_C_mul_X_pow 3 ha]
  rfl

Depends on / 依赖: add_assoc, degree_C_mul_X_pow, degree_add_eq_left_of_degree_lt, degree_quadratic_lt_degree_C_mul_X_cb
-/
theorem degree_cubic (ha : a != 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 := by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [degree_add_eq_left_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [degree_C_mul_X_pow 3 ha]
  rfl

/--
theorem `natDegree_cubic_le` / 定理 `natDegree_cubic_le`

English:
theorem natDegree_cubic_le
  statement: natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3
  proof: natDegree_le_of_degree_le degree_cubic_le

中文:
定理 natDegree_cubic_le
  结论: natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3
  证明: natDegree_le_of_degree_le degree_cubic_le

Depends on / 依赖: degree_cubic_le, natDegree_le_of_degree_le
-/
theorem natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) <= 3 :=
  natDegree_le_of_degree_le degree_cubic_le

/--
theorem `natDegree_cubic` / 定理 `natDegree_cubic`

English:
theorem natDegree_cubic
  given: (ha : a != 0)
  statement: natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3
  proof: natDegree_eq_of_degree_eq_some degree_cubic ha

@[simp]

中文:
定理 natDegree_cubic
  条件: (ha : a != 0)
  结论: natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3
  证明: natDegree_eq_of_degree_eq_some degree_cubic ha

@[simp]

Depends on / 依赖: degree_cubic, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_cubic (ha : a != 0) : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
natDegree_eq_of_degree_eq_some degree_cubic ha

@[simp]
/--
theorem `leadingCoeff_cubic` / 定理 `leadingCoeff_cubic`

English:
theorem leadingCoeff_cubic
  given: (ha : a != 0)
  proof: by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [leadingCoeff_C_mul_X_pow]

中文:
定理 leadingCoeff_cubic
  条件: (ha : a != 0)
  证明: by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [leadingCoeff_C_mul_X_pow]

Depends on / 依赖: add_assoc, add_comm, degree_quadratic_lt_degree_C_mul_X_cb, leadingCoeff_C_mul_X_pow, leadingCoeff_add_of_degree_lt
-/
theorem leadingCoeff_cubic (ha : a != 0) :
    leadingCoeff (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = a := by
  rw [add_assoc]; rw [add_assoc]; rw [← add_assoc (C b * X ^ 2)]; rw [add_comm]; rw [leadingCoeff_add_of_degree_lt degree_quadratic_lt_degree_C_mul_X_cb ha]; rw [leadingCoeff_C_mul_X_pow]

end Semiring

end Polynomial
